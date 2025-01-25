use halo2_base::halo2_proofs::{
    halo2curves::bn256::{Bn256, Fr, G1Affine},
    plonk::{Circuit, VerifyingKey},
    poly::kzg::commitment::ParamsKZG,
};
use rand::{rngs::StdRng, SeedableRng};
use snark_verifier::{
    system::halo2::{compile, Config},
    verifier::plonk::PlonkProtocol,
};

use crate::{Snark, SHPLONK};

use super::{aggregation::AggregationCircuit, gen_dummy_snark_from_vk};

#[derive(Clone, Copy, Debug)]
pub struct AggregationDependencyIntent<'a> {
    pub vk: &'a VerifyingKey<G1Affine>,
    pub num_instance: &'a [usize],
    pub accumulator_indices: Option<&'a [(usize, usize)]>,
    /// See [`AggregationDependencyIntentOwned::agg_vk_hash_data`].
    pub agg_vk_hash_data: Option<((usize, usize), Fr)>,
}

#[derive(Clone, Debug)]
pub struct AggregationDependencyIntentOwned {
    pub vk: VerifyingKey<G1Affine>,
    pub num_instance: Vec<usize>,
    pub accumulator_indices: Option<Vec<(usize, usize)>>,
    /// If this dependency is itself from a universal aggregation circuit, this should contain (index, agg_vkey_hash), where `index = (i,j)` is the pair recording that the agg_vkey_hash is located at `instances[i][j]`.
    pub agg_vk_hash_data: Option<((usize, usize), Fr)>,
}

impl AggregationDependencyIntent<'_> {
    /// Converts `self` into `PlonkProtocol`
    pub fn compile(self, params: &ParamsKZG<Bn256>) -> PlonkProtocol<G1Affine> {
        compile(
            params,
            self.vk,
            Config::kzg()
                .with_num_instance(self.num_instance.to_vec())
                .with_accumulator_indices(self.accumulator_indices.map(|v| v.to_vec())),
        )
    }
}

/// This trait should be implemented on the minimal circuit configuration data necessary to
/// completely determine an aggregation circuit
/// (independent of circuit inputs or specific snarks to be aggregated).
/// This is used to generate a _dummy_ instantiation of a concrete `Circuit` type for the purposes of key generation.
/// This dummy instantiation just needs to have the correct arithmetization format, but the witnesses do not need to
/// satisfy constraints.
///
/// This trait is specialized for aggregation circuits, which need to aggregate **dependency** snarks.
/// The aggregation circuit should only depend on the verifying key of each dependency snark.
pub trait KeygenAggregationCircuitIntent {
    /// Concrete circuit type. Defaults to [`AggregationCircuit`].
    type AggregationCircuit: Circuit<Fr> = AggregationCircuit;

    /// The **ordered** list of [`VerifyingKey`]s of the circuits to be aggregated.
    fn intent_of_dependencies(&self) -> Vec<AggregationDependencyIntent>;

    /// Builds a _dummy_ instantiation of `Self::AggregationCircuit` for the purposes of key generation.
    /// Assumes that `snarks` is an ordered list of [`Snark`]s, where the `i`th snark corresponds to the `i`th [`VerifyingKey`] in `vk_of_dependencies`.
    /// The `snarks` only need to have the correct witness sizes (e.g., proof length) but the
    /// snarks do _not_ need to verify.
    ///
    /// May specify additional custom logic for building the aggregation circuit from the snarks.
    fn build_keygen_circuit_from_snarks(self, snarks: Vec<Snark>) -> Self::AggregationCircuit;

    /// Builds a _dummy_ instantiation of `Self::AggregationCircuit` for the purposes of key generation.
    ///
    /// Generates dummy snarks from the verifying keys in `vk_of_dependencies`, **assuming** that SHPLONK is
    /// used for the multi-open scheme.
    fn build_keygen_circuit_shplonk(self) -> Self::AggregationCircuit
    where
        Self: Sized,
    {
        let mut rng = StdRng::seed_from_u64(0u64);
        let snarks =
            self.intent_of_dependencies()
                .into_iter()
                .map(
                    |AggregationDependencyIntent {
                         vk,
                         num_instance,
                         accumulator_indices,
                         agg_vk_hash_data,
                     }| {
                        let k = vk.get_domain().k();
                        // In KZG `gen_dummy_snark_from_vk` calls `compile`, which only uses `params` for `params.k()` so we can just use a random untrusted setup.
                        // Moreover since this is a dummy snark, the trusted setup shouldn't matter.
                        let params = ParamsKZG::setup(k, &mut rng);
                        let mut snark = gen_dummy_snark_from_vk::<SHPLONK>(
                            &params,
                            vk,
                            num_instance.to_vec(),
                            accumulator_indices.map(|v| v.to_vec()),
                        );
                        // We set the current agg_vk_hash in the dummy snark so that the final agg_vk_hash is correct at the end of keygen.
                        if let Some(((i, j), agg_vk_hash)) = agg_vk_hash_data {
                            assert!(
                            i < snark.instances.len(),
                            "Invalid agg_vk_hash index: ({i},{j}), num_instance: {num_instance:?}");
                            assert!(j < snark.instances[i].len(),
                            "Invalid agg_vk_hash index: ({i},{j}), num_instance: {num_instance:?}");
                            snark.instances[i][j] = agg_vk_hash;
                        }
                        snark
                    },
                )
                .collect();
        self.build_keygen_circuit_from_snarks(snarks)
    }
}

impl<'a> From<&'a AggregationDependencyIntentOwned> for AggregationDependencyIntent<'a> {
    fn from(intent: &'a AggregationDependencyIntentOwned) -> Self {
        Self {
            vk: &intent.vk,
            num_instance: &intent.num_instance,
            accumulator_indices: intent.accumulator_indices.as_deref(),
            agg_vk_hash_data: intent.agg_vk_hash_data,
        }
    }
}
