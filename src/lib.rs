//! This crate is a helper for versioning encoded data.
//! It provides the `Version` trait that defines the version of data and it's encoding and decoding.
//!
//! ```rust
//!    use versionneer::{versioned, Encodable, Decodable, bincode};
//!
//!    #[derive(Debug, thiserror::Error)]
//!    enum Error {
//!        #[error("Invalid version: {0}")]
//!        InvalidVersion(u32),
//!        #[error(transparent)]
//!        Decode(#[from] ::bincode::error::DecodeError),
//!        #[error(transparent)]
//!        Encoder(#[from] ::bincode::error::EncodeError),
//!    }
//!    impl versionneer::Error for Error {
//!        fn invalid_version(version: u32) -> Self {
//!            Self::InvalidVersion(version)
//!        }
//!    }
//!
//!    #[derive(Debug, PartialEq, Eq, ::bincode::Decode, ::bincode::Encode)]
//!    struct TestV0 {
//!        data: u8,
//!    }
//!    versioned!(TestV0, 0);
//!
//!    let mut data = Vec::new();
//!    let mut enc = bincode::Encoder::new(&mut data);
//!    let test = TestV0 { data: 42 };
//!    <TestV0 as Encodable<_, Error>>::encode(&test, &mut enc).expect("Failed to encode");
//!    let mut reader = data.as_slice();
//!    let mut dec = bincode::Decoder::new(&mut reader);
//!    let decoded = <TestV0 as Decodable<_, Error>>::decode(&mut dec).expect("Failed to decode");
//!    assert_eq!(test, decoded);
//! ```
//!
//! In addition it provides the `Upgrade` struct that can be used to create a upgrade chain for versioned data.
//!
//! ```rust
//!    use versionneer::{versioned, Encodable, Decodable, bincode, Upgrade};
//!
//!    #[derive(Debug, thiserror::Error)]
//!    enum Error {
//!        #[error("Invalid version: {0}")]
//!        InvalidVersion(u32),
//!        #[error(transparent)]
//!        Decode(#[from] ::bincode::error::DecodeError),
//!        #[error(transparent)]
//!        Encoder(#[from] ::bincode::error::EncodeError),
//!    }
//!    impl versionneer::Error for Error {
//!        fn invalid_version(version: u32) -> Self {
//!            Self::InvalidVersion(version)
//!        }
//!    }
//!
//!    #[derive(Debug, PartialEq, Eq, ::bincode::Decode, ::bincode::Encode)]
//!    struct TestV0 {
//!        data: u8,
//!    }
//!    versioned!(TestV0, 0);
//!
//!    #[derive(Debug, PartialEq, Eq, ::bincode::Decode, ::bincode::Encode)]
//!    struct TestV1 {
//!        data: u16,
//!    }
//!    versioned!(TestV1, 1);
//!
//!    impl TryFrom<TestV0> for TestV1 {
//!        type Error = Error;
//!        fn try_from(value: TestV0) -> Result<Self, Self::Error> {
//!            Ok(TestV1 { data: u16::from(value.data) })
//!        }
//!    }
//!
//!    type Latest = Upgrade<TestV1, TestV0, Error>;
//!    let mut data = Vec::new();
//!    let mut enc = bincode::Encoder::new(&mut data);
//!    let test = TestV0 { data: 42 };
//!    <TestV0 as Encodable<_, Error>>::encode(&test, &mut enc).expect("Failed to encode");
//!    let mut reader = data.as_slice();
//!    let mut dec = bincode::Decoder::new(&mut reader);
//!    let decoded = Latest::decode(&mut dec).expect("Failed to decode");
//!    assert_eq!(decoded, TestV1 { data: 42 });
//! ```

#![deny(
    warnings,
    clippy::unwrap_used,
    clippy::unnecessary_unwrap,
    clippy::pedantic,
    missing_docs
)]

#[cfg(feature = "bincode")]
/// Bincode encoding and decoding for versionneer
pub mod bincode;

/// Versioning error trait
pub trait Error: std::error::Error {
    /// Create a new error for an invalid version.
    fn invalid_version(version: u32) -> Self;
}

/// A decoder for versionneer it is used to both encode the data as well as the version.
pub trait Decoder {
    /// The error type for the decoder.
    type Error: std::error::Error;
    /// Decodes the version from the decoder.
    ///
    /// # Errors
    /// This function will return an error if the decoder fails to decode the version.
    fn decode_version(&mut self) -> Result<u32, Self::Error>;
}

/// Decode trait for versioned data, it is used in combination with the `Decoder` trait.
///
/// Many decoders will provide a blanket implementation for this trait.
pub trait Decode<D: Decoder>
where
    Self: Sized,
{
    /// Decode the data from the decoder.
    ///
    /// # Errors
    /// This function will return an error if the data cannot be decoded.
    fn decode_data(decoder: &mut D) -> Result<Self, D::Error>;
}

/// The `Encoder` trait is used to encode versioned data.
pub trait Encoder {
    /// The error type for the encoder.
    type Error: std::error::Error;
    /// Encodes the version to the encoder.
    ///
    /// # Errors
    /// This function will return an error if encoder fails to encode the version.
    fn encode_version(&mut self, version: u32) -> Result<(), Self::Error>;
}

/// The `Encode` trait is used to encode versioned data.
///
/// Many `Encoder`s will provide a blanket implementation for this trait.
pub trait Encode<E: Encoder>
where
    Self: Sized,
{
    /// Encodes the data to the encoder.
    ///
    /// # Errors
    /// This function will return an error if encoder fails to encode the data.
    fn encode_data(&self, encoder: &mut E) -> Result<(), E::Error>;
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
pub trait Versioned<Err: Error>: Sized {
    /// The type that the versioned data is encoding
    type Output;
    /// The version tag of this data
    const VERSION: u32;
}

/// This trait is used to mark a versioned type as encodable. Usually this is provided by the `versioned!` macro.
pub trait Encodable<Enc, Err>: Versioned<Err>
where
    Err: Error + From<Enc::Error>,
    Enc: Encoder,
    Self::Output: Encode<Enc>,
{
    /// Encodes the data including the version tag.
    ///
    /// # Errors
    /// - Returns an error if the data failes to encode.
    fn encode(data: &Self::Output, encoder: &mut Enc) -> Result<(), Err> {
        encoder.encode_version(Self::VERSION)?;
        data.encode_data(encoder)?;
        Ok(())
    }
}

/// This trait is used to mark a versioned type as decodable. Usually this is provided by the `versioned!` macro.
pub trait Decodable<Dec, Err>: Versioned<Err>
where
    Err: Error + From<Dec::Error>,
    Dec: Decoder,
    Self::Output: Decode<Dec>,
{
    /// Decodes versioned data and validates the version. Will consume the version from the reader.
    /// # Errors
    /// - Returns an error if the version is invalid.
    /// - Returns an error if the data is invalid.
    fn decode(decoder: &mut Dec) -> Result<Self::Output, Err> {
        let version: u32 = decoder.decode_version()?;
        Self::decode_with_version(decoder, version)
    }

    /// Decodes the data with a provided version tag. Is helpful for use in combination with `Upgrade`.
    ///
    /// # Errors
    /// - Returns an error if the version is invalid.
    /// - Returns an error if the data is invalid.
    #[inline]
    fn decode_with_version(decoder: &mut Dec, version: u32) -> Result<Self::Output, Err> {
        if version == Self::VERSION {
            // We have validated the version, so we can safely decode the body.
            unsafe { Self::decode_body(decoder) }
        } else {
            Err(Err::invalid_version(version))
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
    unsafe fn decode_body(decoder: &mut Dec) -> Result<Self::Output, Err> {
        let data = Self::Output::decode_data(decoder)?;
        Ok(data)
    }
}

/// The `Upgrade` struct is used to upgrade data from a previous version to the latest version.
///
/// `Prior::VERSION` must be less than `Latest::VERSION`!
///
/// Upgrades can be chained!
pub struct Upgrade<Latest, Prior, Err>
where
    Err: Error,
    Prior: Versioned<Err>,
    Latest: Versioned<Err>,
    Latest::Output: TryFrom<Prior::Output>,
{
    _marker: std::marker::PhantomData<(Prior, Latest, Err)>,
}

impl<Latest, Prior, Err> Versioned<Err> for Upgrade<Latest, Prior, Err>
where
    Err: Error,
    Prior: Versioned<Err>,
    Latest: Versioned<Err>,
    Latest::Output: TryFrom<Prior::Output>,
{
    type Output = Latest::Output;
    const VERSION: u32 = Latest::VERSION;
}

impl<Latest, Prior, Enc, Err> Encodable<Enc, Err> for Upgrade<Latest, Prior, Err>
where
    Err: Error + From<<Enc as Encoder>::Error>,
    Enc: Encoder,
    Prior: Versioned<Err>,
    Latest: Versioned<Err>,
    Latest::Output: Encode<Enc>,
    Latest::Output: TryFrom<Prior::Output>,
{
}

impl<Latest, Prior, Dec, Err> Decodable<Dec, Err> for Upgrade<Latest, Prior, Err>
where
    Dec: Decoder,
    Prior: Versioned<Err> + Decodable<Dec, Err>,
    Prior::Output: Decode<Dec>,
    Latest: Versioned<Err> + Decodable<Dec, Err>,
    Latest::Output: TryFrom<Prior::Output> + Decode<Dec>,
    Err: Error
        + From<<Dec as Decoder>::Error>
        + From<<Latest::Output as TryFrom<Prior::Output>>::Error>,
{
    fn decode_with_version(decoder: &mut Dec, version: u32) -> Result<Self::Output, Err> {
        debug_assert!(
            Prior::VERSION < Latest::VERSION,
            "Upgrade versions need to increase! Prior::Version({}) >= Latest::Version({})",
            Prior::VERSION,
            Latest::VERSION
        );
        if version == Latest::VERSION {
            Latest::decode_with_version(decoder, version)
        } else {
            let prior = Prior::decode_with_version(decoder, version)?;
            Ok(Latest::Output::try_from(prior)?)
        }
    }
}

/// This macro is a shortcut to crate a versioned type with the associated `Encodable` and `Decodable` traits.
#[macro_export]
macro_rules! versioned {
    ($type:ty, $ver:expr) => {
        impl<Err> $crate::Versioned<Err> for $type
        where
            Err: $crate::Error,
        {
            type Output = $type;
            const VERSION: u32 = $ver;
        }

        impl<Enc, Err> $crate::Encodable<Enc, Err> for $type
        where
            Err: $crate::Error + From<<Enc as $crate::Encoder>::Error>,
            Enc: $crate::Encoder,
            <Self as $crate::Versioned<Err>>::Output: $crate::Encode<Enc>,
        {
        }

        impl<Dec, Err> $crate::Decodable<Dec, Err> for $type
        where
            Err: $crate::Error + From<<Dec as $crate::Decoder>::Error>,
            Dec: $crate::Decoder,
            <Self as $crate::Versioned<Err>>::Output: $crate::Decode<Dec>,
        {
        }
    };
}
