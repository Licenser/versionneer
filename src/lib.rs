//! This crate is a helper for versioning encoded data.
//! It provides the `Version` trait that defines the version of data and it's encoding and decoding.
//!
//! ```rust
//!     use versionneer::{Upgrade, Versioned};
//!
//!     #[derive(Debug, thiserror::Error)]
//!     enum Error {
//!         #[error("Invalid version: {0}")]
//!         InvalidVersion(u32),
//!         #[error(transparent)]
//!         Decode(#[from] bincode::error::DecodeError),
//!         #[error(transparent)]
//!         Encoder(#[from] bincode::error::EncodeError),
//!     }
//!     impl versionneer::Error for Error {
//!         fn invalid_version(version: u32) -> Self {
//!             Self::InvalidVersion(version)
//!         }
//!     }
//!
//!     #[derive(Debug, PartialEq, Eq, bincode::Decode, bincode::Encode)]
//!     struct TestV0 {
//!         data: u8,
//!     }
//!     impl Versioned<Error> for TestV0 {
//!         type Output = TestV0;
//!         const VERSION: u32 = 0;
//!     }
//!
//!     let mut data = Vec::new();
//!
//!     let test = TestV0 { data: 42 };
//!     TestV0::encode(&test, &mut data).unwrap();
//!
//!     let decoded = TestV0::decode(&mut data.as_slice()).unwrap();
//!     assert_eq!(test, decoded);
//! ```
//!
//! In addition it provides the `Upgrade` struct that can be used to create a upgrade chain for versioned data.
//!
//! ```rust
//!     use versionneer::{Upgrade, Versioned};
//!
//!     #[derive(Debug, thiserror::Error)]
//!     enum Error {
//!         #[error("Invalid version: {0}")]
//!         InvalidVersion(u32),
//!         #[error(transparent)]
//!         Decode(#[from] bincode::error::DecodeError),
//!         #[error(transparent)]
//!         Encoder(#[from] bincode::error::EncodeError),
//!     }
//!     impl versionneer::Error for Error {
//!         fn invalid_version(version: u32) -> Self {
//!             Self::InvalidVersion(version)
//!         }
//!     }
//!
//!     #[derive(Debug, PartialEq, Eq, bincode::Decode, bincode::Encode)]
//!     struct TestV0 {
//!         data: u8,
//!     }
//!
//!     impl Versioned<Error> for TestV0 {
//!         type Output = TestV0;
//!         const VERSION: u32 = 0;
//!     }
//!
//!     #[derive(Debug, PartialEq, Eq, bincode::Decode, bincode::Encode)]
//!     struct TestV1 {
//!         data: u16,
//!     }
//!
//!     impl Versioned<Error> for TestV1 {
//!         type Output = TestV1;
//!         const VERSION: u32 = 1;
//!     }
//!
//!     impl TryFrom<TestV0> for TestV1 {
//!         type Error = Error;
//!         fn try_from(value: TestV0) -> Result<Self, Self::Error> {
//!             Ok(TestV1 { data: value.data as u16 })
//!         }
//!     }
//!
//!     type Test = Upgrade<Error, TestV1, TestV0>;
//!     let mut data = Vec::new();
//!
//!     let test = TestV0 { data: 42 };
//!     TestV0::encode(&test, &mut data).unwrap();
//!
//!     let decoded = Test::decode(&mut data.as_slice()).unwrap();
//!     assert_eq!(decoded, TestV1 { data: 42 });
//! ```
#![deny(
    warnings,
    clippy::unwrap_used,
    clippy::unnecessary_unwrap,
    clippy::pedantic,
    missing_docs
)]

use std::io::{Read, Write};

use bincode::error::{DecodeError, EncodeError};

/// Versioning error trait
pub trait Error: std::error::Error + From<DecodeError> + From<EncodeError> {
    /// Create a new error for an invalid version.
    fn invalid_version(version: u32) -> Self;
}

/// Versioned trait
/// This trait is meant to be implemented either by the struct itself or by a version container.
///
/// The default methods do not need to be changed unelss you want to customize the behaviour of
/// how versions are treated.
///
/// `E` defines the error type for the versioning process and encoding and decoding.
///
/// `Output` defines the type of the data that is being versioned.
///
/// `Version` defines the version of the data that is being versioned.
pub trait Versioned<E: Error>: Sized {
    /// The type that the versioned data is encoding
    type Output: bincode::Decode<()> + bincode::Encode;
    /// The version tag of this data
    const VERSION: u32;

    /// Decodes versioned data and validates the version. Will consume the version from the reader.
    /// # Errors
    /// - Returns an error if the version is invalid.
    /// - Returns an error if the data is invalid.
    fn decode(reader: &mut impl Read) -> Result<Self::Output, E> {
        let config = bincode::config::standard();
        let version: u32 = bincode::decode_from_std_read(reader, config)?;
        Self::decode_with_version(reader, version)
    }

    /// Encodes the data including the version tag.
    ///
    /// # Errors
    /// - Returns an error if the data failes to encode.
    fn encode(data: &Self::Output, writer: &mut impl Write) -> Result<(), E> {
        let config = bincode::config::standard();
        bincode::encode_into_std_write(Self::VERSION, writer, config).map_err(E::from)?;
        bincode::encode_into_std_write(data, writer, config).map_err(E::from)?;
        Ok(())
    }

    /// Decodes the data with a provided version tag. Is helpful for use in combination with `Upgrade`.
    ///
    /// # Errors
    /// - Returns an error if the version is invalid.
    /// - Returns an error if the data is invalid.
    #[inline]
    fn decode_with_version(reader: &mut impl Read, version: u32) -> Result<Self::Output, E> {
        if version == Self::VERSION {
            // We have validated the version, so we can safely decode the body.
            unsafe { Self::decode_body(reader) }
        } else {
            Err(E::invalid_version(version))
        }
    }
    /// Decodes only the body, assuming the version has already been validated.
    ///
    /// # Safety
    /// This function is marked unsafe because it does not validate the version and when
    /// used without care might lead to data corruption or other issues.
    ///
    /// # Errors
    /// - Returns an error if the data is invalid.
    #[inline]
    unsafe fn decode_body(reader: &mut impl Read) -> Result<Self::Output, E> {
        let config = bincode::config::standard();
        bincode::decode_from_std_read(reader, config).map_err(E::from)
    }
}

/// The `Upgrade` struct is used to upgrade data from a previous version to the latest version.
///
/// `Prior::VERSION` must be less than `Latest::VERSION`!
///
/// Upgrades can be chained!
pub struct Upgrade<E, Latest, Prior>
where
    E: Error + From<<Latest::Output as TryFrom<Prior::Output>>::Error>,
    Prior: Versioned<E>,
    Latest: Versioned<E>,
    Latest::Output: TryFrom<Prior::Output>,
{
    _marker: std::marker::PhantomData<(Prior, Latest, E)>,
}
impl<E, Latest, Prior> Upgrade<E, Latest, Prior>
where
    E: Error + From<<Latest::Output as TryFrom<Prior::Output>>::Error>,
    Prior: Versioned<E>,
    Latest: Versioned<E>,
    Latest::Output: TryFrom<Prior::Output>,
{
    /// Creates a new `Upgrade` instance.
    ///
    /// In debug mode this will assert on the version order being correct, however during runtime
    /// correctness is assumed.
    #[must_use]
    pub fn new() -> Self {
        debug_assert!(
            Prior::VERSION < Latest::VERSION,
            "Upgrade versions need to increase! Prior::Version({}) >= Latest::Version({})",
            Prior::VERSION,
            Latest::VERSION
        );
        Self {
            _marker: std::marker::PhantomData,
        }
    }
}

impl<E, Latest, Prior> Default for Upgrade<E, Latest, Prior>
where
    E: Error + From<<Latest::Output as TryFrom<Prior::Output>>::Error>,
    Prior: Versioned<E>,
    Latest: Versioned<E>,
    Latest::Output: TryFrom<Prior::Output>,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<E, Latest, Prior> Versioned<E> for Upgrade<E, Latest, Prior>
where
    E: Error + From<<Latest::Output as TryFrom<Prior::Output>>::Error>,
    Prior: Versioned<E>,
    Latest: Versioned<E>,
    Latest::Output: TryFrom<Prior::Output>,
{
    type Output = Latest::Output;
    const VERSION: u32 = Latest::VERSION;

    fn decode_with_version(reader: &mut impl Read, version: u32) -> Result<Self::Output, E> {
        debug_assert!(
            Prior::VERSION < Latest::VERSION,
            "Upgrade versions need to increase! Prior::Version({}) >= Latest::Version({})",
            Prior::VERSION,
            Latest::VERSION
        );
        if version == Latest::VERSION {
            Latest::decode_with_version(reader, version)
        } else {
            let prior = Prior::decode_with_version(reader, version)?;
            Ok(Latest::Output::try_from(prior)?)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Upgrade, Versioned};

    #[derive(Debug, PartialEq, Eq, bincode::Decode, bincode::Encode)]
    struct TestV0 {
        data: u8,
    }

    #[derive(Debug, PartialEq, Eq, bincode::Decode, bincode::Encode)]
    struct TestV1 {
        data: u16,
    }
    #[derive(Debug, PartialEq, Eq, bincode::Decode, bincode::Encode)]
    struct TestV2 {
        data: u32,
    }

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

    #[derive(Debug, thiserror::Error)]
    enum Error {
        #[error("Invalid version: {0}")]
        InvalidVersion(u32),
        #[error(transparent)]
        Decode(#[from] bincode::error::DecodeError),
        #[error(transparent)]
        Encoder(#[from] bincode::error::EncodeError),
    }
    impl super::Error for Error {
        fn invalid_version(version: u32) -> Self {
            Self::InvalidVersion(version)
        }
    }

    impl Versioned<Error> for TestV0 {
        type Output = Self;
        const VERSION: u32 = 0;
    }

    impl Versioned<Error> for TestV1 {
        type Output = Self;
        const VERSION: u32 = 1;
    }

    impl Versioned<Error> for TestV2 {
        type Output = Self;
        const VERSION: u32 = 2;
    }

    #[test]
    fn test_v1() -> Result<(), Error> {
        let mut data = Vec::new();
        TestV1::encode(&TestV1 { data: 42 }, &mut data)?;
        let mut reader = data.as_slice();
        let v1 = TestV1::decode(&mut reader)?;
        assert_eq!(v1.data, 42);
        Ok(())
    }
    #[test]
    fn test_v0() -> Result<(), Error> {
        let mut data = Vec::new();
        TestV0::encode(&TestV0 { data: 42 }, &mut data)?;
        let mut reader = data.as_slice();
        let v0 = TestV0::decode(&mut reader)?;
        assert_eq!(v0.data, 42);
        Ok(())
    }

    #[test]
    fn test_upgrade_v1() -> Result<(), Error> {
        type Latest = Upgrade<Error, TestV1, TestV0>;
        let mut data = Vec::new();
        TestV0::encode(&TestV0 { data: 42 }, &mut data)?;
        let mut reader = data.as_slice();
        let v1 = Latest::decode(&mut reader)?;
        assert_eq!(v1.data, 42);
        Ok(())
    }
    #[test]
    fn test_upgrade_v2() -> Result<(), Error> {
        type Latest = Upgrade<Error, TestV2, Upgrade<Error, TestV1, TestV0>>;
        let mut data = Vec::new();
        TestV0::encode(&TestV0 { data: 42 }, &mut data)?;
        let mut reader = data.as_slice();
        let v0 = Latest::decode(&mut reader)?;
        assert_eq!(v0.data, 42);
        Ok(())
    }
}
