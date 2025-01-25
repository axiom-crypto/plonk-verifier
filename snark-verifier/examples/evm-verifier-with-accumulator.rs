use aggregation::{AggregationCircuit, AggregationConfigParams};
use halo2_base::{
    gates::circuit::{BaseCircuitParams, CircuitBuilderStage},
    halo2_proofs,
    utils::fs::gen_srs,
};
use halo2_proofs::{
    dev::MockProver,
    halo2curves::bn256::{Bn256, Fq, Fr, G1Affine},
    plonk::{create_proof, keygen_pk, keygen_vk, verify_proof, Circuit, ProvingKey, VerifyingKey},
    poly::{
        commitment::ParamsProver,
        kzg::{
            commitment::{KZGCommitmentScheme, ParamsKZG},
            multiopen::{ProverGWC, VerifierGWC},
            strategy::AccumulatorStrategy,
        },
        VerificationStrategy,
    },
    transcript::{EncodedChallenge, TranscriptReadBuffer, TranscriptWriterBuffer},
};
use itertools::Itertools;
use rand::rngs::OsRng;
#[cfg(feature = "revm")]
use snark_verifier::loader::evm::{deploy_and_call, encode_calldata};
use snark_verifier::{
    loader::{
        evm::{self, EvmLoader},
        native::NativeLoader,
    },
    pcs::kzg::{Gwc19, KzgAs, LimbsEncoding},
    system::halo2::{compile, transcript::evm::EvmTranscript, Config},
    verifier::{self, SnarkVerifier},
};
use std::{fs::File, io::Cursor, rc::Rc};

const LIMBS: usize = 3;
const BITS: usize = 88;

type As = KzgAs<Bn256, Gwc19>;
type PlonkSuccinctVerifier = verifier::plonk::PlonkSuccinctVerifier<As, LimbsEncoding<LIMBS, BITS>>;
type PlonkVerifier = verifier::plonk::PlonkVerifier<As, LimbsEncoding<LIMBS, BITS>>;

mod application {
    use super::halo2_proofs::{
        circuit::{Layouter, SimpleFloorPlanner, Value},
        plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Fixed, Instance},
        poly::Rotation,
    };
    use super::Fr;
    use halo2_base::halo2_proofs::plonk::Assigned;
    use rand::RngCore;

    #[derive(Clone, Copy)]
    pub struct StandardPlonkConfig {
        a: Column<Advice>,
        b: Column<Advice>,
        c: Column<Advice>,
        q_a: Column<Fixed>,
        q_b: Column<Fixed>,
        q_c: Column<Fixed>,
        q_ab: Column<Fixed>,
        constant: Column<Fixed>,
        #[allow(dead_code)]
        instance: Column<Instance>,
    }

    impl StandardPlonkConfig {
        fn configure(meta: &mut ConstraintSystem<Fr>) -> Self {
            let [a, b, c] = [(); 3].map(|_| meta.advice_column());
            let [q_a, q_b, q_c, q_ab, constant] = [(); 5].map(|_| meta.fixed_column());
            let instance = meta.instance_column();

            [a, b, c].map(|column| meta.enable_equality(column));

            meta.create_gate(
                "q_a·a + q_b·b + q_c·c + q_ab·a·b + constant + instance = 0",
                |meta| {
                    let [a, b, c] =
                        [a, b, c].map(|column| meta.query_advice(column, Rotation::cur()));
                    let [q_a, q_b, q_c, q_ab, constant] = [q_a, q_b, q_c, q_ab, constant]
                        .map(|column| meta.query_fixed(column, Rotation::cur()));
                    let instance = meta.query_instance(instance, Rotation::cur());
                    Some(
                        q_a * a.clone()
                            + q_b * b.clone()
                            + q_c * c
                            + q_ab * a * b
                            + constant
                            + instance,
                    )
                },
            );

            StandardPlonkConfig { a, b, c, q_a, q_b, q_c, q_ab, constant, instance }
        }
    }

    #[derive(Clone, Default)]
    pub struct StandardPlonk(Fr);

    impl StandardPlonk {
        pub fn rand<R: RngCore>(mut rng: R) -> Self {
            Self(Fr::from(rng.next_u32() as u64))
        }

        pub fn num_instance() -> Vec<usize> {
            vec![1]
        }

        pub fn instances(&self) -> Vec<Vec<Fr>> {
            vec![vec![self.0]]
        }
    }

    impl Circuit<Fr> for StandardPlonk {
        type Config = StandardPlonkConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
            meta.set_minimum_degree(4);
            StandardPlonkConfig::configure(meta)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fr>,
        ) -> Result<(), Error> {
            layouter.assign_region(
                || "",
                |mut region| {
                    #[cfg(feature = "halo2-pse")]
                    {
                        region.assign_advice(|| "", config.a, 0, || Value::known(self.0))?;
                        region.assign_fixed(|| "", config.q_a, 0, || Value::known(-Fr::one()))?;

                        region.assign_advice(
                            || "",
                            config.a,
                            1,
                            || Value::known(-Fr::from(5u64)),
                        )?;
                        for (idx, column) in (1..).zip([
                            config.q_a,
                            config.q_b,
                            config.q_c,
                            config.q_ab,
                            config.constant,
                        ]) {
                            region.assign_fixed(
                                || "",
                                column,
                                1,
                                || Value::known(Fr::from(idx as u64)),
                            )?;
                        }

                        let a =
                            region.assign_advice(|| "", config.a, 2, || Value::known(Fr::one()))?;
                        a.copy_advice(|| "", &mut region, config.b, 3)?;
                        a.copy_advice(|| "", &mut region, config.c, 4)?;
                    }
                    #[cfg(feature = "halo2-axiom")]
                    {
                        region.assign_advice(config.a, 0, Value::known(Assigned::Trivial(self.0)));
                        region.assign_fixed(config.q_a, 0, Assigned::Trivial(-Fr::one()));

                        region.assign_advice(
                            config.a,
                            1,
                            Value::known(Assigned::Trivial(-Fr::from(5u64))),
                        );
                        for (idx, column) in (1..).zip([
                            config.q_a,
                            config.q_b,
                            config.q_c,
                            config.q_ab,
                            config.constant,
                        ]) {
                            region.assign_fixed(column, 1, Assigned::Trivial(Fr::from(idx as u64)));
                        }

                        let a = region.assign_advice(
                            config.a,
                            2,
                            Value::known(Assigned::Trivial(Fr::one())),
                        );
                        a.copy_advice(&mut region, config.b, 3);
                        a.copy_advice(&mut region, config.c, 4);
                    }

                    Ok(())
                },
            )
        }
    }
}

mod aggregation {
    use crate::PlonkSuccinctVerifier;

    use super::{As, BITS, LIMBS};
    use super::{Fr, G1Affine};
    use halo2_base::gates::{
        circuit::{builder::BaseCircuitBuilder, BaseCircuitParams, CircuitBuilderStage},
        flex_gate::MultiPhaseThreadBreakPoints,
    };
    use halo2_ecc::bn254::FpChip;
    use itertools::Itertools;
    use rand::rngs::OsRng;
    use snark_verifier::{
        loader::{self, native::NativeLoader},
        pcs::{
            kzg::{KzgAccumulator, KzgSuccinctVerifyingKey},
            AccumulationScheme, AccumulationSchemeProver,
        },
        system,
        util::arithmetic::fe_to_limbs,
        verifier::{plonk::PlonkProtocol, SnarkVerifier},
    };
    use std::{mem, rc::Rc};

    const T: usize = 3;
    const RATE: usize = 2;
    const R_F: usize = 8;
    const R_P: usize = 57;
    const SECURE_MDS: usize = 0;

    type Svk = KzgSuccinctVerifyingKey<G1Affine>;
    type BaseFieldEccChip<'chip> = halo2_ecc::ecc::BaseFieldEccChip<'chip, G1Affine>;
    type Halo2Loader<'chip> = loader::halo2::Halo2Loader<G1Affine, BaseFieldEccChip<'chip>>;
    pub type PoseidonTranscript<L, S> =
        system::halo2::transcript::halo2::PoseidonTranscript<G1Affine, L, S, T, RATE, R_F, R_P>;

    #[derive(Clone)]
    pub struct Snark {
        protocol: PlonkProtocol<G1Affine>,
        instances: Vec<Vec<Fr>>,
        proof: Vec<u8>,
    }

    impl Snark {
        pub fn new(
            protocol: PlonkProtocol<G1Affine>,
            instances: Vec<Vec<Fr>>,
            proof: Vec<u8>,
        ) -> Self {
            Self { protocol, instances, proof }
        }
    }

    impl Snark {
        fn proof(&self) -> &[u8] {
            self.proof.as_slice()
        }
    }

    pub fn aggregate<'a>(
        svk: &Svk,
        loader: &Rc<Halo2Loader<'a>>,
        snarks: &[Snark],
        as_proof: &[u8],
    ) -> KzgAccumulator<G1Affine, Rc<Halo2Loader<'a>>> {
        let assign_instances = |instances: &[Vec<Fr>]| {
            instances
                .iter()
                .map(|instances| {
                    instances.iter().map(|instance| loader.assign_scalar(*instance)).collect_vec()
                })
                .collect_vec()
        };

        let accumulators = snarks
            .iter()
            .flat_map(|snark| {
                let protocol = snark.protocol.loaded(loader);
                let instances = assign_instances(&snark.instances);
                let mut transcript =
                    PoseidonTranscript::<Rc<Halo2Loader>, _>::new::<0>(loader, snark.proof());
                let proof =
                    PlonkSuccinctVerifier::read_proof(svk, &protocol, &instances, &mut transcript)
                        .unwrap();
                PlonkSuccinctVerifier::verify(svk, &protocol, &instances, &proof).unwrap()
            })
            .collect_vec();

        let mut transcript =
            PoseidonTranscript::<Rc<Halo2Loader>, _>::new::<SECURE_MDS>(loader, as_proof);
        let proof = As::read_proof(&Default::default(), &accumulators, &mut transcript).unwrap();
        As::verify(&Default::default(), &accumulators, &proof).unwrap()
    }

    #[derive(serde::Serialize, serde::Deserialize, Default)]
    pub struct AggregationConfigParams {
        pub degree: u32,
        pub num_advice: usize,
        pub num_lookup_advice: usize,
        pub num_fixed: usize,
        pub lookup_bits: usize,
    }

    #[derive(Clone, Debug)]
    pub struct AggregationCircuit {
        pub inner: BaseCircuitBuilder<Fr>,
        #[allow(dead_code)]
        pub as_proof: Vec<u8>,
    }

    impl AggregationCircuit {
        pub fn new(
            stage: CircuitBuilderStage,
            circuit_params: BaseCircuitParams,
            break_points: Option<MultiPhaseThreadBreakPoints>,
            params_g0: G1Affine,
            snarks: impl IntoIterator<Item = Snark>,
        ) -> Self {
            let svk: Svk = params_g0.into();
            let snarks = snarks.into_iter().collect_vec();

            // verify the snarks natively to get public instances
            let accumulators = snarks
                .iter()
                .flat_map(|snark| {
                    let mut transcript = PoseidonTranscript::<NativeLoader, _>::new::<SECURE_MDS>(
                        snark.proof.as_slice(),
                    );
                    let proof = PlonkSuccinctVerifier::read_proof(
                        &svk,
                        &snark.protocol,
                        &snark.instances,
                        &mut transcript,
                    )
                    .unwrap();
                    PlonkSuccinctVerifier::verify(&svk, &snark.protocol, &snark.instances, &proof)
                        .unwrap()
                })
                .collect_vec();

            let (_accumulator, as_proof) = {
                let mut transcript =
                    PoseidonTranscript::<NativeLoader, _>::new::<SECURE_MDS>(Vec::new());
                let accumulator =
                    As::create_proof(&Default::default(), &accumulators, &mut transcript, OsRng)
                        .unwrap();
                (accumulator, transcript.finalize())
            };

            let mut builder = BaseCircuitBuilder::from_stage(stage).use_params(circuit_params);
            // create halo2loader
            let range = builder.range_chip();
            let fp_chip = FpChip::<Fr>::new(&range, BITS, LIMBS);
            let ecc_chip = BaseFieldEccChip::new(&fp_chip);
            let pool = mem::take(builder.pool(0));
            let loader = Halo2Loader::new(ecc_chip, pool);

            // witness generation
            let KzgAccumulator { lhs, rhs } =
                aggregate(&svk, &loader, &snarks, as_proof.as_slice());
            let lhs = lhs.assigned();
            let rhs = rhs.assigned();
            let assigned_instances = lhs
                .x()
                .limbs()
                .iter()
                .chain(lhs.y().limbs().iter())
                .chain(rhs.x().limbs().iter())
                .chain(rhs.y().limbs().iter())
                .copied()
                .collect_vec();

            #[cfg(debug_assertions)]
            {
                let KzgAccumulator { lhs, rhs } = _accumulator;
                let instances =
                    [lhs.x, lhs.y, rhs.x, rhs.y].map(fe_to_limbs::<_, Fr, LIMBS, BITS>).concat();
                for (lhs, rhs) in instances.iter().zip(assigned_instances.iter()) {
                    assert_eq!(lhs, rhs.value());
                }
            }

            *builder.pool(0) = loader.take_ctx();
            builder.assigned_instances[0] = assigned_instances;
            if let Some(break_points) = break_points {
                builder.set_break_points(break_points);
            }
            Self { inner: builder, as_proof }
        }

        pub fn num_instance() -> Vec<usize> {
            // [..lhs, ..rhs]
            vec![4 * LIMBS]
        }

        pub fn instances(&self) -> Vec<Vec<Fr>> {
            self.inner
                .assigned_instances
                .iter()
                .map(|v| v.iter().map(|v| *v.value()).collect_vec())
                .collect()
        }

        pub fn accumulator_indices() -> Vec<(usize, usize)> {
            (0..4 * LIMBS).map(|idx| (0, idx)).collect()
        }
    }
}

fn gen_pk<C: Circuit<Fr>>(params: &ParamsKZG<Bn256>, circuit: &C) -> ProvingKey<G1Affine> {
    let vk = keygen_vk(params, circuit).unwrap();
    println!("finished vk");
    let pk = keygen_pk(params, vk, circuit).unwrap();
    println!("finished pk");
    pk
}

fn gen_proof<
    C: Circuit<Fr>,
    E: EncodedChallenge<G1Affine>,
    TR: TranscriptReadBuffer<Cursor<Vec<u8>>, G1Affine, E>,
    TW: TranscriptWriterBuffer<Vec<u8>, G1Affine, E>,
>(
    params: &ParamsKZG<Bn256>,
    pk: &ProvingKey<G1Affine>,
    circuit: C,
    instances: Vec<Vec<Fr>>,
) -> Vec<u8> {
    let instances = instances.iter().map(|instances| instances.as_slice()).collect_vec();
    let proof = {
        let mut transcript = TW::init(Vec::new());
        create_proof::<KZGCommitmentScheme<Bn256>, ProverGWC<_>, _, _, TW, _>(
            params,
            pk,
            &[circuit],
            &[instances.as_slice()],
            OsRng,
            &mut transcript,
        )
        .unwrap();
        transcript.finalize()
    };

    let accept = {
        let mut transcript = TR::init(Cursor::new(proof.clone()));
        VerificationStrategy::<_, VerifierGWC<_>>::finalize(
            verify_proof::<_, VerifierGWC<_>, _, TR, _>(
                params.verifier_params(),
                pk.get_vk(),
                AccumulatorStrategy::new(params.verifier_params()),
                &[instances.as_slice()],
                &mut transcript,
            )
            .unwrap(),
        )
    };
    assert!(accept);

    proof
}

fn gen_application_snark(params: &ParamsKZG<Bn256>) -> aggregation::Snark {
    let circuit = application::StandardPlonk::rand(OsRng);

    let pk = gen_pk(params, &circuit);
    let protocol = compile(
        params,
        pk.get_vk(),
        Config::kzg().with_num_instance(application::StandardPlonk::num_instance()),
    );

    let proof = gen_proof::<
        _,
        _,
        aggregation::PoseidonTranscript<NativeLoader, _>,
        aggregation::PoseidonTranscript<NativeLoader, _>,
    >(params, &pk, circuit.clone(), circuit.instances());
    aggregation::Snark::new(protocol, circuit.instances(), proof)
}

fn gen_aggregation_evm_verifier(
    params: &ParamsKZG<Bn256>,
    vk: &VerifyingKey<G1Affine>,
    num_instance: Vec<usize>,
    accumulator_indices: Vec<(usize, usize)>,
) -> Vec<u8> {
    let protocol = compile(
        params,
        vk,
        Config::kzg()
            .with_num_instance(num_instance.clone())
            .with_accumulator_indices(Some(accumulator_indices)),
    );
    let vk = (params.get_g()[0], params.g2(), params.s_g2()).into();

    let loader = EvmLoader::new::<Fq, Fr>();
    let protocol = protocol.loaded(&loader);
    let mut transcript = EvmTranscript::<_, Rc<EvmLoader>, _, _>::new(&loader);

    let instances = transcript.load_instances(num_instance);
    let proof = PlonkVerifier::read_proof(&vk, &protocol, &instances, &mut transcript).unwrap();
    PlonkVerifier::verify(&vk, &protocol, &instances, &proof).unwrap();

    evm::compile_solidity(&loader.solidity_code())
}

#[cfg(feature = "revm")]
fn evm_verify(deployment_code: Vec<u8>, instances: Vec<Vec<Fr>>, proof: Vec<u8>) {
    let calldata = encode_calldata(&instances, &proof);
    let gas_cost = deploy_and_call(deployment_code, calldata).unwrap();
    dbg!(gas_cost);
}

fn main() {
    let params_app = gen_srs(8);

    let snarks = [(); 3].map(|_| gen_application_snark(&params_app));

    let path = "./configs/example_evm_accumulator.json";
    let agg_config: AggregationConfigParams = serde_json::from_reader(
        File::open(path).unwrap_or_else(|e| panic!("{path} does not exist: {e:?}")),
    )
    .unwrap();
    let mut circuit_params = BaseCircuitParams {
        k: agg_config.degree as usize,
        num_advice_per_phase: vec![agg_config.num_advice],
        num_lookup_advice_per_phase: vec![agg_config.num_lookup_advice],
        num_fixed: agg_config.num_fixed,
        lookup_bits: Some(agg_config.lookup_bits),
        num_instance_columns: 1,
    };
    let mut agg_circuit = AggregationCircuit::new(
        CircuitBuilderStage::Mock,
        circuit_params,
        None,
        params_app.get_g()[0],
        snarks.clone(),
    );
    circuit_params = agg_circuit.inner.calculate_params(Some(9));
    #[cfg(debug_assertions)]
    {
        MockProver::run(agg_config.degree, &agg_circuit.inner, agg_circuit.instances())
            .unwrap()
            .assert_satisfied();
        println!("mock prover passed");
    }

    let params = gen_srs(agg_config.degree);
    let pk = gen_pk(&params, &agg_circuit.inner);
    let _deployment_code = gen_aggregation_evm_verifier(
        &params,
        pk.get_vk(),
        aggregation::AggregationCircuit::num_instance(),
        aggregation::AggregationCircuit::accumulator_indices(),
    );

    let break_points = agg_circuit.inner.break_points();
    drop(agg_circuit);

    let agg_circuit = AggregationCircuit::new(
        CircuitBuilderStage::Prover,
        circuit_params,
        Some(break_points),
        params_app.get_g()[0],
        snarks,
    );
    let instances = agg_circuit.instances();
    let _proof = gen_proof::<
        _,
        _,
        EvmTranscript<G1Affine, _, _, _>,
        EvmTranscript<G1Affine, _, _, _>,
    >(&params, &pk, agg_circuit.inner, instances.clone());
    #[cfg(feature = "revm")]
    evm_verify(_deployment_code, instances, _proof);
}
