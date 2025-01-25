//! Transcript for verifier in [`halo2_proofs`] circuit.

use crate::halo2_proofs;
use crate::util::arithmetic::FieldExt;
use crate::{
    loader::{
        halo2::{EcPoint, EccInstructions, Halo2Loader, Scalar},
        native::{self, NativeLoader},
        Loader, ScalarLoader,
    },
    util::{
        arithmetic::{fe_to_fe, CurveAffine, PrimeField},
        hash::{OptimizedPoseidonSpec, Poseidon},
        transcript::{Transcript, TranscriptRead, TranscriptWrite},
        Itertools,
    },
    Error,
};
use halo2_proofs::transcript::EncodedChallenge;
use std::{
    io::{self, Read, Write},
    rc::Rc,
};

/// Encoding that encodes elliptic curve point into native field elements.
pub trait NativeEncoding<C>: EccInstructions<C>
where
    C: CurveAffine,
{
    /// Encode.
    fn encode(
        &self,
        ctx: &mut Self::Context,
        ec_point: &Self::AssignedEcPoint,
    ) -> Result<Vec<Self::AssignedScalar>, Error>;
}

/// A way to keep track of what gets read in the transcript.
#[derive(Clone, Debug)]
pub enum TranscriptObject<C, L>
where
    C: CurveAffine,
    L: Loader<C>,
{
    /// Scalar
    Scalar(L::LoadedScalar),
    /// Elliptic curve point
    EcPoint(L::LoadedEcPoint),
}

#[derive(Debug)]
/// Transcript for verifier in [`halo2_proofs`] circuit using poseidon hasher.
/// Currently It assumes the elliptic curve scalar field is same as native
/// field.
pub struct PoseidonTranscript<
    C,
    L,
    S,
    const T: usize,
    const RATE: usize,
    const R_F: usize,
    const R_P: usize,
> where
    C: CurveAffine,
    L: Loader<C>,
{
    loader: L,
    stream: S,
    /// Only relevant for Halo2 loader: as elements from `stream` are read, they are assigned as witnesses.
    /// The loaded witnesses are pushed to `loaded_stream`. This way at the end we have the entire proof transcript
    /// as loaded witnesses.
    pub loaded_stream: Vec<TranscriptObject<C, L>>,
    buf: Poseidon<C::Scalar, <L as ScalarLoader<C::Scalar>>::LoadedScalar, T, RATE>,
}

impl<C, R, EccChip, const T: usize, const RATE: usize, const R_F: usize, const R_P: usize>
    PoseidonTranscript<C, Rc<Halo2Loader<C, EccChip>>, R, T, RATE, R_F, R_P>
where
    C: CurveAffine,
    R: Read,
    EccChip: NativeEncoding<C>,
{
    /// Initialize [`PoseidonTranscript`] given readable or writeable stream for
    /// verifying or proving with [`NativeLoader`].
    pub fn new<const SECURE_MDS: usize>(loader: &Rc<Halo2Loader<C, EccChip>>, stream: R) -> Self
    where
        C::Scalar: FieldExt,
    {
        let buf = Poseidon::new::<R_F, R_P, SECURE_MDS>(loader);
        Self { loader: loader.clone(), stream, buf, loaded_stream: vec![] }
    }

    /// Initialize [`PoseidonTranscript`] from a precomputed spec of round constants and MDS matrix because computing the constants is expensive.
    pub fn from_spec(
        loader: &Rc<Halo2Loader<C, EccChip>>,
        stream: R,
        spec: OptimizedPoseidonSpec<C::Scalar, T, RATE>,
    ) -> Self {
        let buf = Poseidon::from_spec(loader, spec);
        Self { loader: loader.clone(), stream, buf, loaded_stream: vec![] }
    }

    /// Clear the buffer and set the stream to a new one. Effectively the same as starting from a new transcript.
    pub fn new_stream(&mut self, stream: R) {
        self.buf.clear();
        self.loaded_stream.clear();
        self.stream = stream;
    }
}

impl<C, R, EccChip, const T: usize, const RATE: usize, const R_F: usize, const R_P: usize>
    Transcript<C, Rc<Halo2Loader<C, EccChip>>>
    for PoseidonTranscript<C, Rc<Halo2Loader<C, EccChip>>, R, T, RATE, R_F, R_P>
where
    C: CurveAffine,
    R: Read,
    EccChip: NativeEncoding<C>,
{
    fn loader(&self) -> &Rc<Halo2Loader<C, EccChip>> {
        &self.loader
    }

    fn squeeze_challenge(&mut self) -> Scalar<C, EccChip> {
        self.buf.squeeze()
    }

    fn common_scalar(&mut self, scalar: &Scalar<C, EccChip>) -> Result<(), Error> {
        self.buf.update(&[scalar.clone()]);
        Ok(())
    }

    fn common_ec_point(&mut self, ec_point: &EcPoint<C, EccChip>) -> Result<(), Error> {
        let encoded = self
            .loader
            .ecc_chip()
            .encode(&mut self.loader.ctx_mut(), &ec_point.assigned())
            .map(|encoded| {
                encoded
                    .into_iter()
                    .map(|encoded| self.loader.scalar_from_assigned(encoded))
                    .collect_vec()
            })
            .map_err(|_| {
                Error::Transcript(
                    io::ErrorKind::Other,
                    "Failed to encode elliptic curve point into native field elements".to_string(),
                )
            })?;
        self.buf.update(&encoded);
        Ok(())
    }
}

impl<C, R, EccChip, const T: usize, const RATE: usize, const R_F: usize, const R_P: usize>
    TranscriptRead<C, Rc<Halo2Loader<C, EccChip>>>
    for PoseidonTranscript<C, Rc<Halo2Loader<C, EccChip>>, R, T, RATE, R_F, R_P>
where
    C: CurveAffine,
    R: Read,
    EccChip: NativeEncoding<C>,
{
    fn read_scalar(&mut self) -> Result<Scalar<C, EccChip>, Error> {
        let scalar = {
            let mut data = <C::Scalar as PrimeField>::Repr::default();
            self.stream.read_exact(data.as_mut()).unwrap();
            C::Scalar::from_repr(data).unwrap()
        };
        let scalar = self.loader.assign_scalar(scalar);
        self.loaded_stream.push(TranscriptObject::Scalar(scalar.clone()));
        self.common_scalar(&scalar)?;
        Ok(scalar)
    }

    fn read_ec_point(&mut self) -> Result<EcPoint<C, EccChip>, Error> {
        let ec_point = {
            let mut compressed = C::Repr::default();
            self.stream.read_exact(compressed.as_mut()).unwrap();
            C::from_bytes(&compressed).unwrap()
        };
        let ec_point = self.loader.assign_ec_point(ec_point);
        self.loaded_stream.push(TranscriptObject::EcPoint(ec_point.clone()));
        self.common_ec_point(&ec_point)?;
        Ok(ec_point)
    }
}

impl<C: CurveAffine, S, const T: usize, const RATE: usize, const R_F: usize, const R_P: usize>
    PoseidonTranscript<C, NativeLoader, S, T, RATE, R_F, R_P>
{
    /// Initialize [`PoseidonTranscript`] given readable or writeable stream for
    /// verifying or proving with [`NativeLoader`].
    pub fn new<const SECURE_MDS: usize>(stream: S) -> Self
    where
        C::Scalar: FieldExt,
    {
        Self {
            loader: NativeLoader,
            stream,
            buf: Poseidon::new::<R_F, R_P, SECURE_MDS>(&NativeLoader),
            loaded_stream: vec![],
        }
    }

    /// Initialize [`PoseidonTranscript`] from a precomputed spec of round constants and MDS matrix because computing the constants is expensive.
    pub fn from_spec(stream: S, spec: OptimizedPoseidonSpec<C::Scalar, T, RATE>) -> Self {
        Self {
            loader: NativeLoader,
            stream,
            buf: Poseidon::from_spec(&NativeLoader, spec),
            loaded_stream: vec![],
        }
    }

    /// Clear the buffer and set the stream to a new one. Effectively the same as starting from a new transcript.
    pub fn new_stream(&mut self, stream: S) {
        self.buf.clear();
        self.loaded_stream.clear();
        self.stream = stream;
    }
}

impl<C: CurveAffine, const T: usize, const RATE: usize, const R_F: usize, const R_P: usize>
    PoseidonTranscript<C, NativeLoader, Vec<u8>, T, RATE, R_F, R_P>
{
    /// Clear the buffer and stream.
    pub fn clear(&mut self) {
        self.buf.clear();
        self.loaded_stream.clear();
        self.stream.clear();
    }
}

impl<C: CurveAffine, S, const T: usize, const RATE: usize, const R_F: usize, const R_P: usize>
    Transcript<C, NativeLoader> for PoseidonTranscript<C, NativeLoader, S, T, RATE, R_F, R_P>
{
    fn loader(&self) -> &NativeLoader {
        &native::LOADER
    }

    fn squeeze_challenge(&mut self) -> C::Scalar {
        self.buf.squeeze()
    }

    fn common_scalar(&mut self, scalar: &C::Scalar) -> Result<(), Error> {
        self.buf.update(&[*scalar]);
        Ok(())
    }

    fn common_ec_point(&mut self, ec_point: &C) -> Result<(), Error> {
        let encoded: Vec<_> = Option::from(ec_point.coordinates().map(|coordinates| {
            [coordinates.x(), coordinates.y()].into_iter().cloned().map(fe_to_fe).collect_vec()
        }))
        .ok_or_else(|| {
            Error::Transcript(
                io::ErrorKind::Other,
                "Invalid elliptic curve point encoding in proof".to_string(),
            )
        })?;
        self.buf.update(&encoded);
        Ok(())
    }
}

impl<C, R, const T: usize, const RATE: usize, const R_F: usize, const R_P: usize>
    TranscriptRead<C, NativeLoader> for PoseidonTranscript<C, NativeLoader, R, T, RATE, R_F, R_P>
where
    C: CurveAffine,
    R: Read,
{
    fn read_scalar(&mut self) -> Result<C::Scalar, Error> {
        let mut data = <C::Scalar as PrimeField>::Repr::default();
        self.stream
            .read_exact(data.as_mut())
            .map_err(|err| Error::Transcript(err.kind(), err.to_string()))?;
        let scalar = C::Scalar::from_repr_vartime(data).ok_or_else(|| {
            Error::Transcript(io::ErrorKind::Other, "Invalid scalar encoding in proof".to_string())
        })?;
        self.loaded_stream.push(TranscriptObject::Scalar(scalar));
        self.common_scalar(&scalar)?;
        Ok(scalar)
    }

    fn read_ec_point(&mut self) -> Result<C, Error> {
        let mut data = C::Repr::default();
        self.stream
            .read_exact(data.as_mut())
            .map_err(|err| Error::Transcript(err.kind(), err.to_string()))?;
        let ec_point = Option::<C>::from(C::from_bytes(&data)).ok_or_else(|| {
            Error::Transcript(
                io::ErrorKind::Other,
                "Invalid elliptic curve point encoding in proof".to_string(),
            )
        })?;
        self.loaded_stream.push(TranscriptObject::EcPoint(ec_point));
        self.common_ec_point(&ec_point)?;
        Ok(ec_point)
    }
}

impl<C, W, const T: usize, const RATE: usize, const R_F: usize, const R_P: usize>
    PoseidonTranscript<C, NativeLoader, W, T, RATE, R_F, R_P>
where
    C: CurveAffine,
    W: Write,
{
    /// Returns mutable `stream`.
    pub fn stream_mut(&mut self) -> &mut W {
        &mut self.stream
    }

    /// Finalize transcript and returns `stream`.
    pub fn finalize(self) -> W {
        self.stream
    }
}

impl<C, W, const T: usize, const RATE: usize, const R_F: usize, const R_P: usize> TranscriptWrite<C>
    for PoseidonTranscript<C, NativeLoader, W, T, RATE, R_F, R_P>
where
    C: CurveAffine,
    W: Write,
{
    fn write_scalar(&mut self, scalar: C::Scalar) -> Result<(), Error> {
        self.common_scalar(&scalar)?;
        let data = scalar.to_repr();
        self.stream_mut().write_all(data.as_ref()).map_err(|err| {
            Error::Transcript(err.kind(), "Failed to write scalar to transcript".to_string())
        })
    }

    fn write_ec_point(&mut self, ec_point: C) -> Result<(), Error> {
        self.common_ec_point(&ec_point)?;
        let data = ec_point.to_bytes();
        self.stream_mut().write_all(data.as_ref()).map_err(|err| {
            Error::Transcript(
                err.kind(),
                "Failed to write elliptic curve to transcript".to_string(),
            )
        })
    }
}

/// [`EncodedChallenge`] implemented for verifier in [`halo2_proofs`] circuit.
/// Currently It assumes the elliptic curve scalar field is same as native
/// field.
#[derive(Debug)]
pub struct ChallengeScalar<C: CurveAffine>(C::Scalar);

impl<C: CurveAffine> EncodedChallenge<C> for ChallengeScalar<C> {
    type Input = C::Scalar;

    fn new(challenge_input: &C::Scalar) -> Self {
        ChallengeScalar(*challenge_input)
    }

    fn get_scalar(&self) -> C::Scalar {
        self.0
    }
}

impl<C: CurveAffine, S, const T: usize, const RATE: usize, const R_F: usize, const R_P: usize>
    halo2_proofs::transcript::Transcript<C, ChallengeScalar<C>>
    for PoseidonTranscript<C, NativeLoader, S, T, RATE, R_F, R_P>
{
    fn squeeze_challenge(&mut self) -> ChallengeScalar<C> {
        ChallengeScalar::new(&Transcript::squeeze_challenge(self))
    }

    fn common_point(&mut self, ec_point: C) -> io::Result<()> {
        match Transcript::common_ec_point(self, &ec_point) {
            Err(Error::Transcript(kind, msg)) => Err(io::Error::new(kind, msg)),
            Err(_) => unreachable!(),
            _ => Ok(()),
        }
    }

    fn common_scalar(&mut self, scalar: C::Scalar) -> io::Result<()> {
        match Transcript::common_scalar(self, &scalar) {
            Err(Error::Transcript(kind, msg)) => Err(io::Error::new(kind, msg)),
            Err(_) => unreachable!(),
            _ => Ok(()),
        }
    }
}

impl<C, R, const T: usize, const RATE: usize, const R_F: usize, const R_P: usize>
    halo2_proofs::transcript::TranscriptRead<C, ChallengeScalar<C>>
    for PoseidonTranscript<C, NativeLoader, R, T, RATE, R_F, R_P>
where
    C: CurveAffine,
    R: Read,
{
    fn read_point(&mut self) -> io::Result<C> {
        match TranscriptRead::read_ec_point(self) {
            Err(Error::Transcript(kind, msg)) => Err(io::Error::new(kind, msg)),
            Err(_) => unreachable!(),
            Ok(value) => Ok(value),
        }
    }

    fn read_scalar(&mut self) -> io::Result<C::Scalar> {
        match TranscriptRead::read_scalar(self) {
            Err(Error::Transcript(kind, msg)) => Err(io::Error::new(kind, msg)),
            Err(_) => unreachable!(),
            Ok(value) => Ok(value),
        }
    }
}

impl<C, R, const T: usize, const RATE: usize, const R_F: usize, const R_P: usize>
    halo2_proofs::transcript::TranscriptReadBuffer<R, C, ChallengeScalar<C>>
    for PoseidonTranscript<C, NativeLoader, R, T, RATE, R_F, R_P>
where
    C: CurveAffine,
    C::Scalar: FieldExt,
    R: Read,
{
    fn init(reader: R) -> Self {
        Self::new::<0>(reader)
    }
}

impl<C, W, const T: usize, const RATE: usize, const R_F: usize, const R_P: usize>
    halo2_proofs::transcript::TranscriptWrite<C, ChallengeScalar<C>>
    for PoseidonTranscript<C, NativeLoader, W, T, RATE, R_F, R_P>
where
    C: CurveAffine,
    W: Write,
{
    fn write_point(&mut self, ec_point: C) -> io::Result<()> {
        halo2_proofs::transcript::Transcript::<C, ChallengeScalar<C>>::common_point(
            self, ec_point,
        )?;
        let data = ec_point.to_bytes();
        self.stream_mut().write_all(data.as_ref())
    }

    fn write_scalar(&mut self, scalar: C::Scalar) -> io::Result<()> {
        halo2_proofs::transcript::Transcript::<C, ChallengeScalar<C>>::common_scalar(self, scalar)?;
        let data = scalar.to_repr();
        self.stream_mut().write_all(data.as_ref())
    }
}

impl<C, W, const T: usize, const RATE: usize, const R_F: usize, const R_P: usize>
    halo2_proofs::transcript::TranscriptWriterBuffer<W, C, ChallengeScalar<C>>
    for PoseidonTranscript<C, NativeLoader, W, T, RATE, R_F, R_P>
where
    C: CurveAffine,
    C::Scalar: FieldExt,
    W: Write,
{
    fn init(writer: W) -> Self {
        Self::new::<0>(writer)
    }

    fn finalize(self) -> W {
        self.finalize()
    }
}

mod halo2_lib {
    use crate::system::halo2::transcript::halo2::NativeEncoding;
    use halo2_base::utils::{BigPrimeField, CurveAffineExt};
    use halo2_ecc::ecc::BaseFieldEccChip;

    impl<C: CurveAffineExt> NativeEncoding<C> for BaseFieldEccChip<'_, C>
    where
        C::Scalar: BigPrimeField,
        C::Base: BigPrimeField,
    {
        fn encode(
            &self,
            _: &mut Self::Context,
            ec_point: &Self::AssignedEcPoint,
        ) -> Result<Vec<Self::AssignedScalar>, crate::Error> {
            Ok(vec![*ec_point.x().native(), *ec_point.y().native()])
        }
    }
}
