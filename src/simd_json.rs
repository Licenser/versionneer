use std::io::Write;

use simd_json::{
    Error as JsonError, ErrorType, Node, Tape,
    derived::{TypedScalarValue, ValueObjectAccessAsScalar},
};
use simd_json_derive::Serialize;

use crate::{Decode, Encode};

/// Bincode decoder using `std::io::Read`
pub struct Decoder<'data> {
    tape: Option<Tape<'data>>,
}

impl<'data> Decoder<'data> {
    /// Create a new decoder from a reader
    /// # Errors
    /// if the json is invalid
    pub fn new(data: &'data mut [u8]) -> Result<Self, DecodeError> {
        let tape = simd_json::to_tape(data)?;
        Ok(Self { tape: Some(tape) })
    }
}

impl crate::Decoder for Decoder<'_> {
    type Error = DecodeError;
    fn decode_version(&mut self) -> Result<u32, Self::Error> {
        self.tape
            .as_ref()
            .ok_or(DecodeError::AlreadyConsumed)?
            .as_value()
            .get_u32("v")
            .ok_or(DecodeError::InvalidVersionField)
    }
}

#[derive(Debug)]
/// Errors for decoding versioned data with simd-json
pub enum DecodeError {
    /// A simd-json related error
    Json(JsonError),
    /// Derive error
    JsonDerive(simd_json_derive::de::Error),
    /// The version field is missing or not an integer
    InvalidVersionField,
    /// Invalid number of fields
    InvalidNumberOfFields(usize),
    /// Invalid format
    InvalidFormat,
    /// The deserializer was already consumed
    AlreadyConsumed,
}

impl std::error::Error for DecodeError {}

impl std::fmt::Display for DecodeError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            DecodeError::Json(error) => error.fmt(f),
            DecodeError::JsonDerive(error) => error.fmt(f),
            DecodeError::InvalidVersionField => {
                write!(f, "`version` field missing or not an intege")
            }
            DecodeError::InvalidNumberOfFields(n) => write!(
                f,
                "the versioned struct needs to have exactly two elements but has {n}"
            ),
            DecodeError::InvalidFormat => write!(
                f,
                "the format is invalid, needs to be an object with version and data key"
            ),
            DecodeError::AlreadyConsumed => write!(f, "the deserializer was already consumed"),
        }
    }
}
impl From<JsonError> for DecodeError {
    fn from(value: JsonError) -> Self {
        Self::Json(value)
    }
}

impl From<simd_json_derive::de::Error> for DecodeError {
    fn from(value: simd_json_derive::de::Error) -> Self {
        Self::JsonDerive(value)
    }
}

impl<'data, T> Decode<Decoder<'data>> for T
where
    T: simd_json_derive::Deserialize<'data> + 'data,
{
    fn decode_data(decoder: &mut Decoder<'data>) -> Result<Self, DecodeError> {
        let mut tape = decoder
            .tape
            .take()
            .ok_or(DecodeError::AlreadyConsumed)?
            .0
            .into_iter()
            .peekable();

        let Some(Node::Object { len, .. }) = tape.next() else {
            return Err(JsonError::generic(ErrorType::ExpectedMap).into());
        };
        if len != 2 {
            return Err(DecodeError::InvalidNumberOfFields(len));
        }

        // we checked the first to b
        loop {
            let Some(Node::String(key)) = tape.next() else {
                return Err(JsonError::generic(ErrorType::Eof).into());
            };
            if key == "v" {
                match tape.next() {
                    None => return Err(JsonError::generic(ErrorType::Eof).into()),
                    Some(Node::Static(s)) if !s.is_u32() => {
                        return Err(DecodeError::InvalidFormat);
                    }
                    _ => continue,
                }
            }
            if key != "d" {
                return Err(DecodeError::InvalidFormat);
            }

            return Ok(T::from_tape(&mut tape)?);
        }
    }
}

/// Error while encoding versiond data
#[derive(Debug)]
pub enum EncodeError {
    /// A simd-json related error
    Io(std::io::Error),
    /// Version is already set
    VersionAlreadyDefined,
    /// Version not defined
    VersionNotDefined,
}
impl std::error::Error for EncodeError {}

impl From<std::io::Error> for EncodeError {
    fn from(value: std::io::Error) -> Self {
        Self::Io(value)
    }
}
impl std::fmt::Display for EncodeError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            EncodeError::Io(error) => error.fmt(f),
            EncodeError::VersionAlreadyDefined => write!(f, "version already defined"),
            EncodeError::VersionNotDefined => write!(f, "version not defined"),
        }
    }
}
/// Bincode encoder using `std::io::Write`
pub struct Encoder<W: Write> {
    writer: W,
    version: Option<u32>,
}

impl<W: Write> Encoder<W> {
    /// Create a new encoder from a writer
    #[must_use]
    pub fn new(writer: W) -> Self {
        Self {
            writer,
            version: None,
        }
    }
}

impl<W: Write> crate::Encoder for Encoder<W> {
    type Error = EncodeError;
    fn encode_version(&mut self, version: u32) -> Result<(), Self::Error> {
        if self.version.replace(version).is_some() {
            Err(EncodeError::VersionAlreadyDefined)
        } else {
            Ok(())
        }
    }
}

impl<W, T> Encode<Encoder<W>> for T
where
    T: simd_json_derive::Serialize,
    W: Write,
{
    fn encode_data(&self, encoder: &mut Encoder<W>) -> Result<(), EncodeError> {
        let Some(version) = encoder.version else {
            return Err(EncodeError::VersionNotDefined);
        };
        encoder.writer.write_all(br#"{"v":"#)?;
        version.json_write(&mut encoder.writer)?;
        encoder.writer.write_all(br#","d":"#)?;
        self.json_write(&mut encoder.writer)?;
        encoder.writer.write_all(b"}")?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {

    use super::{DecodeError, Decoder, EncodeError, Encoder};
    use crate::{Decodable, Encodable, Upgrade, versioned};

    #[derive(Debug, thiserror::Error)]
    enum Error {
        #[error("Invalid version: {0}")]
        InvalidVersion(u32),
        #[error(transparent)]
        Decode(#[from] DecodeError),
        #[error(transparent)]
        Encoder(#[from] EncodeError),
    }
    impl crate::Error for Error {
        fn invalid_version(version: u32) -> Self {
            Self::InvalidVersion(version)
        }
    }

    #[derive(Debug, PartialEq, Eq, simd_json_derive::Deserialize, simd_json_derive::Serialize)]
    struct TestV0 {
        data: u8,
    }
    versioned!(TestV0, 0);

    #[derive(Debug, PartialEq, Eq, simd_json_derive::Deserialize, simd_json_derive::Serialize)]
    struct TestV1 {
        data: u16,
    }
    versioned!(TestV1, 1);

    #[derive(Debug, PartialEq, Eq, simd_json_derive::Deserialize, simd_json_derive::Serialize)]
    struct TestV2 {
        data: u32,
    }
    versioned!(TestV2, 2);

    impl TryFrom<TestV0> for TestV1 {
        type Error = Error;
        fn try_from(v0: TestV0) -> Result<Self, Self::Error> {
            Ok(Self {
                data: u16::from(v0.data),
            })
        }
    }

    impl TryFrom<TestV1> for TestV2 {
        type Error = Error;
        fn try_from(v1: TestV1) -> Result<Self, Self::Error> {
            Ok(Self {
                data: u32::from(v1.data),
            })
        }
    }

    #[test]
    fn test_v0() -> Result<(), Error> {
        let mut data = Vec::new();
        let mut enc = Encoder::new(&mut data);
        <TestV0 as Encodable<_, Error>>::encode(&TestV0 { data: 42 }, &mut enc)?;
        let mut dec = Decoder::new(data.as_mut_slice())?;
        let v0 = <TestV0 as Decodable<_, Error>>::decode(&mut dec)?;
        assert_eq!(v0.data, 42);
        Ok(())
    }

    #[test]
    fn test_v1() -> Result<(), Error> {
        let mut data = Vec::new();
        let mut enc = Encoder::new(&mut data);
        <TestV1 as Encodable<_, Error>>::encode(&TestV1 { data: 42 }, &mut enc)?;
        let mut dec = Decoder::new(data.as_mut_slice())?;
        let v1 = <TestV1 as Decodable<_, Error>>::decode(&mut dec)?;
        assert_eq!(v1.data, 42);
        Ok(())
    }

    #[test]
    fn test_upgrade_v1() -> Result<(), Error> {
        type Latest = Upgrade<TestV1, TestV0, Error>;
        let mut data = Vec::new();
        let mut enc = Encoder::new(&mut data);
        <TestV0 as Encodable<_, Error>>::encode(&TestV0 { data: 42 }, &mut enc)?;
        let mut dec = Decoder::new(data.as_mut_slice())?;
        let v1 = Latest::decode(&mut dec)?;
        assert_eq!(v1.data, 42);
        Ok(())
    }
    #[test]
    fn test_upgrade_v2() -> Result<(), Error> {
        type Latest = Upgrade<TestV2, TestV1, Error>;
        let mut data = Vec::new();
        let mut enc = Encoder::new(&mut data);
        <TestV1 as Encodable<_, Error>>::encode(&TestV1 { data: 42 }, &mut enc)?;
        let mut dec = Decoder::new(data.as_mut_slice())?;
        let v0 = Latest::decode(&mut dec)?;
        assert_eq!(v0.data, 42);
        Ok(())
    }
    #[test]
    fn test_upgrade_all() -> Result<(), Error> {
        type Latest = Upgrade<TestV2, Upgrade<TestV1, TestV0, Error>, Error>;
        let mut data = Vec::new();
        let mut enc = Encoder::new(&mut data);
        <TestV0 as Encodable<_, Error>>::encode(&TestV0 { data: 42 }, &mut enc)?;
        let mut dec = Decoder::new(data.as_mut_slice())?;
        let v0 = Latest::decode(&mut dec)?;
        assert_eq!(v0.data, 42);
        Ok(())
    }
}
