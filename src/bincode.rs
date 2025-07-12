use std::io::{Read, Write};

use crate::{Decode, Encode};

/// Bincode decoder using `std::io::Read`
pub struct Decoder<R: Read> {
    reader: R,
}

impl<R: Read> Decoder<R> {
    /// Create a new decoder from a reader
    #[must_use]
    pub fn new(reader: R) -> Self {
        Self { reader }
    }
}

impl<R: Read> crate::Decoder for Decoder<R> {
    type Error = bincode::error::DecodeError;
    fn decode_version(&mut self) -> Result<u32, Self::Error> {
        bincode::decode_from_std_read(&mut self.reader, bincode::config::standard())
    }
}

impl<R, T> Decode<Decoder<R>> for T
where
    T: bincode::Decode<()>,
    R: Read,
{
    fn decode_data(decoder: &mut Decoder<R>) -> Result<Self, bincode::error::DecodeError> {
        bincode::decode_from_std_read(&mut decoder.reader, bincode::config::standard())
    }
}

/// Bincode encoder using `std::io::Write`
pub struct Encoder<W: Write> {
    writer: W,
}

impl<W: Write> Encoder<W> {
    /// Create a new encoder from a writer
    #[must_use]
    pub fn new(writer: W) -> Self {
        Self { writer }
    }
}

impl<W: Write> crate::Encoder for Encoder<W> {
    type Error = bincode::error::EncodeError;
    fn encode_version(&mut self, version: u32) -> Result<(), Self::Error> {
        bincode::encode_into_std_write(version, &mut self.writer, bincode::config::standard())?;
        Ok(())
    }
}

impl<W, T> Encode<Encoder<W>> for T
where
    T: bincode::Encode,
    W: Write,
{
    fn encode_data(&self, encoder: &mut Encoder<W>) -> Result<(), bincode::error::EncodeError> {
        bincode::encode_into_std_write(self, &mut encoder.writer, bincode::config::standard())?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {

    use crate::{
        Decodable, Encodable, Upgrade,
        bincode::{Decoder, Encoder},
        versioned,
    };

    #[derive(Debug, thiserror::Error)]
    enum Error {
        #[error("Invalid version: {0}")]
        InvalidVersion(u32),
        #[error(transparent)]
        Decode(#[from] bincode::error::DecodeError),
        #[error(transparent)]
        Encoder(#[from] bincode::error::EncodeError),
    }
    impl crate::Error for Error {
        fn invalid_version(version: u32) -> Self {
            Self::InvalidVersion(version)
        }
    }

    #[derive(Debug, PartialEq, Eq, bincode::Decode, bincode::Encode)]
    struct TestV0 {
        data: u8,
    }
    versioned!(TestV0, 0);

    #[derive(Debug, PartialEq, Eq, bincode::Decode, bincode::Encode)]
    struct TestV1 {
        data: u16,
    }
    versioned!(TestV1, 1);

    #[derive(Debug, PartialEq, Eq, bincode::Decode, bincode::Encode)]
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
        let mut reader = data.as_slice();
        let mut dec = Decoder::new(&mut reader);
        let v0 = <TestV0 as Decodable<_, Error>>::decode(&mut dec)?;
        assert_eq!(v0.data, 42);
        Ok(())
    }

    #[test]
    fn test_v1() -> Result<(), Error> {
        let mut data = Vec::new();
        let mut enc = Encoder::new(&mut data);
        <TestV1 as Encodable<_, Error>>::encode(&TestV1 { data: 42 }, &mut enc)?;
        let mut reader = data.as_slice();
        let mut dec = Decoder::new(&mut reader);
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
        let mut reader = data.as_slice();
        let mut dec = Decoder::new(&mut reader);
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
        let mut reader = data.as_slice();
        let mut dec = Decoder::new(&mut reader);
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
        let mut reader = data.as_slice();
        let mut dec = Decoder::new(&mut reader);
        let v0 = Latest::decode(&mut dec)?;
        assert_eq!(v0.data, 42);
        Ok(())
    }
}
