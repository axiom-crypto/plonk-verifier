use ark_std::{end_timer, start_timer};
use halo2_base::halo2_proofs;
use halo2_base::utils::fs::gen_srs;
use halo2_proofs::halo2curves::bn256::Fr;
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;
use snark_verifier::loader::native::NativeLoader;
use snark_verifier_sdk::{
    self,
    evm::{
        evm_verify, gen_evm_proof_gwc, gen_evm_proof_shplonk, gen_evm_verifier_gwc,
        gen_evm_verifier_shplonk,
    },
    gen_pk,
    halo2::{
        aggregation::load_verify_circuit_degree, aggregation::AggregationCircuit, gen_proof_gwc,
        gen_proof_shplonk, gen_snark_gwc, gen_snark_shplonk, PoseidonTranscript, POSEIDON_SPEC,
    },
    CircuitExt, SHPLONK,
};
use std::env::{set_var, var};
use std::path::Path;

use criterion::{criterion_group, criterion_main};
use criterion::{BenchmarkId, Criterion};
use pprof::criterion::{Output, PProfProfiler};

pub mod zkevm {
    use super::Fr;
    use bus_mapping::{circuit_input_builder::CircuitsParams, mock::BlockData};
    use eth_types::geth_types::GethData;
    use mock::TestContext;
    use zkevm_circuits::{
        evm_circuit::{witness::block_convert, EvmCircuit},
        state_circuit::StateCircuit,
        witness::RwMap,
    };

    pub fn test_evm_circuit() -> EvmCircuit<Fr> {
        let empty_data: GethData =
            TestContext::<0, 0>::new(None, |_| {}, |_, _| {}, |b, _| b).unwrap().into();

        let mut builder = BlockData::new_from_geth_data_with_params(
            empty_data.clone(),
            CircuitsParams::default(),
        )
        .new_circuit_input_builder();

        builder.handle_block(&empty_data.eth_block, &empty_data.geth_traces).unwrap();

        let block = block_convert(&builder.block, &builder.code_db).unwrap();

        EvmCircuit::<Fr>::new(block)
    }

    pub fn test_state_circuit() -> StateCircuit<Fr> {
        StateCircuit::new(RwMap::default(), 1 << 16)
    }
}

fn bench(c: &mut Criterion) {
    let mut rng = ChaCha20Rng::from_entropy();
    let mut transcript =
        PoseidonTranscript::<NativeLoader, _>::from_spec(vec![], POSEIDON_SPEC.clone());

    // === create zkevm evm circuit snark ===
    let k: u32 = var("DEGREE")
        .unwrap_or_else(|_| {
            set_var("DEGREE", "18");
            "18".to_owned()
        })
        .parse()
        .unwrap();
    let evm_circuit = zkevm::test_evm_circuit();
    let state_circuit = zkevm::test_state_circuit();
    let params_app = gen_srs(k);
    let evm_snark = {
        let pk = gen_pk(&params_app, &evm_circuit, Some(Path::new("data/zkevm_evm.pkey")));
        gen_snark_shplonk(&params_app, &pk, evm_circuit, None::<&str>)
    };
    let state_snark = {
        let pk = gen_pk(&params_app, &state_circuit, Some(Path::new("data/zkevm_state.pkey")));
        gen_snark_shplonk(&params_app, &pk, state_circuit, None::<&str>)
    };
    let snarks = [evm_snark, state_snark];
    // === finished zkevm evm circuit ===

    // === now to do aggregation ===
    let path = "./configs/bench_zkevm_plus_state.json";
    // everything below exact same as in zkevm bench
    let agg_config = AggregationConfigParams::from_path(path);
    let k = agg_config.degree;
    let lookup_bits = k as usize - 1;
    let params = gen_srs(k);

    let agg_circuit = AggregationCircuit::keygen::<SHPLONK>(&params, snarks.clone());

    let start1 = start_timer!(|| "gen vk & pk");
    let pk = gen_pk(&params, &agg_circuit, None);
    end_timer!(start1);
    let break_points = agg_circuit.break_points();

    #[cfg(feature = "loader_evm")]
    {
        let start2 = start_timer!(|| "Create EVM SHPLONK proof");
        let agg_circuit = AggregationCircuit::new::<SHPLONK>(
            CircuitBuilderStage::Prover,
            Some(break_points.clone()),
            lookup_bits,
            &params,
            snarks.clone(),
        );
        let instances = agg_circuit.instances();
        let num_instances = agg_circuit.num_instance();

        let proof = gen_evm_proof_shplonk(&params, &pk, agg_circuit, instances.clone());
        end_timer!(start2);

        let deployment_code = gen_evm_verifier_shplonk::<AggregationCircuit>(
            &params,
            pk.get_vk(),
            num_instances.clone(),
            None,
        );

        evm_verify(deployment_code, instances.clone(), proof).expect("evm_verify should succeed");

        let start2 = start_timer!(|| "Create EVM GWC proof");
        let agg_circuit = AggregationCircuit::new::<SHPLONK>(
            CircuitBuilderStage::Prover,
            Some(break_points.clone()),
            lookup_bits,
            &params,
            snarks.clone(),
        );
        let proof = gen_evm_proof_gwc(&params, &pk, agg_circuit, instances.clone());
        end_timer!(start2);

        let deployment_code = gen_evm_verifier_gwc::<AggregationCircuit>(
            &params,
            pk.get_vk(),
            num_instances.clone(),
            None,
        );

        evm_verify(deployment_code, instances, proof).expect("evm_verify should succeed");
    }

    // run benches
    let mut group = c.benchmark_group("shplonk-proof");
    group.sample_size(10);
    group.bench_with_input(
        BenchmarkId::new("zkevm-evm-agg", k),
        &(&params, &pk, &break_points, &snarks),
        |b, &(params, pk, break_points, snarks)| {
            b.iter(|| {
                let agg_circuit = AggregationCircuit::new::<SHPLONK>(
                    CircuitBuilderStage::Prover,
                    Some(break_points.clone()),
                    lookup_bits,
                    params,
                    snarks.clone(),
                );
                let instances = agg_circuit.instances();
                gen_proof_shplonk(params, pk, agg_circuit, instances, None)
            })
        },
    );
    group.finish();

    let mut group = c.benchmark_group("gwc-proof");
    group.sample_size(10);
    group.bench_with_input(
        BenchmarkId::new("zkevm-evm-agg", k),
        &(&params, &pk, &break_points, &snarks),
        |b, &(params, pk, break_points, snarks)| {
            b.iter(|| {
                // note that the generic here remains SHPLONK because it reflects the multi-open scheme for the previous snark (= the zkevm snark)
                let agg_circuit = AggregationCircuit::new::<SHPLONK>(
                    CircuitBuilderStage::Prover,
                    Some(break_points.clone()),
                    lookup_bits,
                    params,
                    snarks.clone(),
                );
                let instances = agg_circuit.instances();
                gen_proof_gwc(params, pk, agg_circuit, instances, None)
            })
        },
    );
    group.finish();
}

criterion_group!(benches, bench);
criterion_main!(benches);
