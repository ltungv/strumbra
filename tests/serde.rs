#![cfg(feature = "serde")]

use std::{collections::HashMap, hash::Hash};

use quickcheck_macros::quickcheck;
use serde::{Deserialize, Serialize};
use strumbra::{SharedString, UniqueString};

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
