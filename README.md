# versionneer ![Build Status] [![Latest Version]][crates.io]

[Build Status]: https://github.com/Licenser/versionneer/workflows/Rust/badge.svg
[Latest Version]: https://img.shields.io/crates/v/versionneer.svg
[crates.io]: https://crates.io/crates/versionneer

A simple version management crate for encoded data that allows for simple versioning and upgrading of data structures.

```rust
   use versionneer::{versioned, Encodable, Decodable, bincode, Upgrade};

   #[derive(Debug, thiserror::Error)]
   enum Error {
       #[error("Invalid version: {0}")]
       InvalidVersion(u32),
       #[error(transparent)]
       Decode(#[from] ::bincode::error::DecodeError),
       #[error(transparent)]
       Encoder(#[from] ::bincode::error::EncodeError),
   }
   impl versionneer::Error for Error {
       fn invalid_version(version: u32) -> Self {
           Self::InvalidVersion(version)
       }
   }

   #[derive(Debug, PartialEq, Eq, ::bincode::Decode, ::bincode::Encode)]
   struct TestV0 {
       data: u8,
   }
   versioned!(TestV0, 0, Error);

   #[derive(Debug, PartialEq, Eq, ::bincode::Decode, ::bincode::Encode)]
   struct TestV1 {
       data: u16,
   }
   versioned!(TestV1, 1, Error);

   impl TryFrom<TestV0> for TestV1 {
       type Error = Error;
       fn try_from(value: TestV0) -> Result<Self, Self::Error> {
           Ok(TestV1 { data: u16::from(value.data) })
       }
   }

   type Latest = Upgrade<TestV1, TestV0, Error>;
   let mut data = Vec::new();
   let mut enc = bincode::Encoder::new(&mut data);
   let test = TestV0 { data: 42 };
   TestV0::encode(&test, &mut enc).expect("Failed to encode");
   let mut reader = data.as_slice();
   let mut dec = bincode::Decoder::new(&mut reader);
   let decoded = Latest::decode(&mut dec).expect("Failed to decode");
   assert_eq!(decoded, TestV1 { data: 42 });
```
