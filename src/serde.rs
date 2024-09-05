//! (De)serialization for [`UmbraString`]

use std::{fmt, marker::PhantomData};

use crate::{
    heap::{ThinAsBytes, ThinDrop},
    SharedString, UmbraString, UniqueString,
};

struct Visitor<B>(PhantomData<B>);

impl<'v, B> serde::de::Visitor<'v> for Visitor<B>
where
    B: ThinDrop + From<Vec<u8>> + for<'b> From<&'b [u8]>,
{
    type Value = UmbraString<B>;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("a string")
    }

    fn visit_string<E>(self, s: String) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        UmbraString::try_from(s).map_err(serde::de::Error::custom)
    }

    fn visit_str<E>(self, s: &str) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        UmbraString::try_from(s).map_err(serde::de::Error::custom)
    }

    fn visit_borrowed_str<E>(self, s: &'v str) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        UmbraString::try_from(s).map_err(serde::de::Error::custom)
    }
}

impl<B> serde::Serialize for UmbraString<B>
where
    B: ThinDrop + ThinAsBytes,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.as_str().serialize(serializer)
    }
}

impl<'de> serde::Deserialize<'de> for UniqueString {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        deserializer.deserialize_string(Visitor(PhantomData))
    }
}

impl<'de> serde::Deserialize<'de> for SharedString {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        deserializer.deserialize_str(Visitor(PhantomData))
    }
}

#[cfg(test)]
#[cfg(feature = "serde")]
mod tests {
    use std::{collections::HashMap, hash::Hash};

    use quickcheck_macros::quickcheck;
    use serde::{Deserialize, Serialize};

    use crate::{SharedString, UniqueString};

    #[derive(Serialize, Deserialize)]
    struct Test<T: Eq + Hash> {
        raw: T,
        vec: Vec<T>,
        map: HashMap<T, T>,
    }

    #[quickcheck]
    #[cfg_attr(miri, ignore)]
    fn serde(raw: String, vec: Vec<String>, map: HashMap<String, String>) {
        let wanted = Test { raw, vec, map };
        let json = serde_json::to_string(&wanted).unwrap();
        let unique = serde_json::from_str::<Test<UniqueString>>(&json).unwrap();
        let shared = serde_json::from_str::<Test<SharedString>>(&json).unwrap();
        assert_eq!(wanted.raw, unique.raw);
        assert_eq!(wanted.raw, shared.raw);
        assert_eq!(wanted.vec, unique.vec);
        assert_eq!(wanted.vec, shared.vec);

        for (k, v) in wanted.map {
            let unique_v = unique.map.get(k.as_str()).expect("A existing value");
            let shared_v = shared.map.get(k.as_str()).expect("A existing value");
            assert_eq!(&v, unique_v);
            assert_eq!(&v, shared_v);
        }
    }
}
