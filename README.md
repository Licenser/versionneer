# versionneer ![Build Status] [![Latest Version]][crates.io]

[Build Status]: https://github.com/Licenser/versionneer/workflows/Rust/badge.svg
[Latest Version]: https://img.shields.io/crates/v/versionneer.svg
[crates.io]: https://crates.io/crates/versionneer

A simple version management crate for encoded data that allows for simple versioning and upgrading of data structures.

```rust
    use versionneer::{Upgrade, Versioned};
    #[derive(Debug, thiserror::Error)]
    enum Error {
        #[error("Invalid version: {0}")]
        InvalidVersion(u32),
        #[error(transparent)]
        Decode(#[from] bincode::error::DecodeError),
        #[error(transparent)]
        Encoder(#[from] bincode::error::EncodeError),
    }
    impl versionneer::Error for Error {
        fn invalid_version(version: u32) -> Self {
            Self::InvalidVersion(version)
        }
    }
    #[derive(Debug, PartialEq, Eq, bincode::Decode, bincode::Encode)]
    struct TestV0 {
        data: u8,
    }
    impl Versioned<Error> for TestV0 {
        type Output = TestV0;
        const VERSION: u32 = 0;
    }
    #[derive(Debug, PartialEq, Eq, bincode::Decode, bincode::Encode)]
    struct TestV1 {
        data: u16,
    }
    impl Versioned<Error> for TestV1 {
        type Output = TestV1;
        const VERSION: u32 = 1;
    }
    impl TryFrom<TestV0> for TestV1 {
        type Error = Error;
        fn try_from(value: TestV0) -> Result<Self, Self::Error> {
            Ok(TestV1 { data: value.data as u16 })
        }
    }
    type Test = Upgrade<Error, TestV1, TestV0>;
    let mut data = Vec::new();
    let test = TestV0 { data: 42 };
    TestV0::encode(&test, &mut data).unwrap();
    let decoded = Test::decode(&mut data.as_slice()).unwrap();
    assert_eq!(decoded, TestV1 { data: 42 });
```
