use std::{cmp, thread};

use quickcheck_macros::quickcheck;
use strumbra::{SharedString, UniqueString};

#[test]
fn test_size_of() {
    assert_eq!(16, std::mem::size_of::<UniqueString>());
    assert_eq!(16, std::mem::size_of::<SharedString>());
}

// NOTE: This is currently mark as UB by miri, so it's ignored. Check the related TODO.
#[test]
#[cfg_attr(miri, ignore)]
fn test_construct_inlined() {
    let unique = UniqueString::try_from("hello world").expect("A valid Umbra-style string");
    let shared = SharedString::try_from("hello world").expect("A valid Umbra-style string");
    assert_eq!("hello world", unique.as_ref());
    assert_eq!("hello world", shared.as_ref());
}

#[test]
fn test_construct_allocated() {
    let unique =
        UniqueString::try_from("Good Morning, Vietnam").expect("A valid Umbra-style string");
    let shared =
        SharedString::try_from("Good Morning, Vietnam").expect("A valid Umbra-style string");
    assert_eq!("Good Morning, Vietnam", unique.as_ref());
    assert_eq!("Good Morning, Vietnam", shared.as_ref());
}

#[test]
fn test_move_across_threads_inlined() {
    let unique = UniqueString::try_from("hello world").expect("A valid Umbra-style string");
    let shared = SharedString::try_from("hello world").expect("A valid Umbra-style string");

    let handles: Vec<_> = (0..8)
        .map(|_| {
            let cloned0 = unique.clone();
            let cloned1 = shared.clone();
            thread::spawn(move || assert_eq!(cloned0, cloned1))
        })
        .collect();

    for handle in handles {
        handle.join().expect("Thread finishes successfully");
    }
}

#[test]
fn test_move_across_threads_allocated() {
    let unique =
        UniqueString::try_from("Good Morning, Vietnam").expect("A valid Umbra-style string");
    let shared =
        SharedString::try_from("Good Morning, Vietnam").expect("A valid Umbra-style string");

    let handles: Vec<_> = (0..8)
        .map(|_| {
            let cloned0 = unique.clone();
            let cloned1 = shared.clone();
            thread::spawn(move || assert_eq!(cloned0, cloned1))
        })
        .collect();

    for handle in handles {
        handle.join().expect("Thread finishes successfully");
    }
}

#[quickcheck]
#[cfg_attr(miri, ignore)]
fn test_format_debug(s: String) {
    let expected = format!("{s:?}");
    let unique = UniqueString::try_from(s.as_str()).expect("A valid Umbra-style string");
    let shared = SharedString::try_from(s.as_str()).expect("A valid Umbra-style string");
    assert_eq!(expected, format!("{unique:?}"));
    assert_eq!(expected, format!("{shared:?}"));
}

#[quickcheck]
#[cfg_attr(miri, ignore)]
fn test_format_display(s: String) {
    let unique = UniqueString::try_from(s.as_str()).expect("A valid Umbra-style string");
    let shared = SharedString::try_from(s.as_str()).expect("A valid Umbra-style string");
    assert_eq!(s, format!("{unique}"));
    assert_eq!(s, format!("{shared}"));
}

#[quickcheck]
#[cfg_attr(miri, ignore)]
fn test_eq(s: String) {
    let unique = UniqueString::try_from(s.as_str()).expect("A valid Umbra-style string");
    let shared = SharedString::try_from(s.as_str()).expect("A valid Umbra-style string");
    assert_eq!(unique, unique);
    assert_eq!(unique, shared);
    assert_eq!(shared, unique);
    assert_eq!(shared, shared);
}

#[quickcheck]
#[cfg_attr(miri, ignore)]
fn test_eq_str(s: String) {
    let unique = UniqueString::try_from(s.as_str()).expect("A valid Umbra-style string");
    let shared = SharedString::try_from(s.as_str()).expect("A valid Umbra-style string");
    assert_eq!(s.as_str(), unique);
    assert_eq!(s.as_str(), shared);
}

#[quickcheck]
#[cfg_attr(miri, ignore)]
fn test_eq_string(s: String) {
    let unique = UniqueString::try_from(s.as_str()).expect("A valid Umbra-style string");
    let shared = SharedString::try_from(s.as_str()).expect("A valid Umbra-style string");
    assert_eq!(s, unique);
    assert_eq!(s, shared);
}

#[quickcheck]
#[cfg_attr(miri, ignore)]
fn test_ne(s1: String, s2: String) {
    let lhs_unique = UniqueString::try_from(s1.as_str()).expect("A valid Umbra-style string");
    let rhs_unique = UniqueString::try_from(s2.as_str()).expect("A valid Umbra-style string");
    let lhs_shared = SharedString::try_from(s1.as_str()).expect("A valid Umbra-style string");
    let rhs_shared = SharedString::try_from(s2.as_str()).expect("A valid Umbra-style string");
    assert_ne!(lhs_unique, rhs_unique);
    assert_ne!(lhs_unique, rhs_shared);
    assert_ne!(lhs_shared, rhs_unique);
    assert_ne!(lhs_shared, rhs_shared);
}

#[quickcheck]
#[cfg_attr(miri, ignore)]
fn test_ne_str(s1: String, s2: String) {
    let lhs_unique = UniqueString::try_from(s1.as_str()).expect("A valid Umbra-style string");
    let rhs_unique = UniqueString::try_from(s2.as_str()).expect("A valid Umbra-style string");
    let lhs_shared = SharedString::try_from(s1.as_str()).expect("A valid Umbra-style string");
    let rhs_shared = SharedString::try_from(s2.as_str()).expect("A valid Umbra-style string");
    assert_ne!(s1.as_str(), rhs_unique);
    assert_ne!(s1.as_str(), rhs_shared);
    assert_ne!(lhs_unique, *s2.as_str());
    assert_ne!(lhs_shared, *s2.as_str());
}

#[quickcheck]
#[cfg_attr(miri, ignore)]
fn test_ne_string(s1: String, s2: String) {
    let lhs_unique = UniqueString::try_from(s1.as_str()).expect("A valid Umbra-style string");
    let rhs_unique = UniqueString::try_from(s2.as_str()).expect("A valid Umbra-style string");
    let lhs_shared = SharedString::try_from(s1.as_str()).expect("A valid Umbra-style string");
    let rhs_shared = SharedString::try_from(s2.as_str()).expect("A valid Umbra-style string");
    assert_ne!(s1, rhs_unique);
    assert_ne!(s1, rhs_shared);
    assert_ne!(lhs_unique, s2);
    assert_ne!(lhs_shared, s2);
}

#[quickcheck]
#[cfg_attr(miri, ignore)]
fn test_cmp_same(s: String) {
    let unique = UniqueString::try_from(s.as_str()).expect("A valid Umbra-style string");
    let shared = SharedString::try_from(s.as_str()).expect("A valid Umbra-style string");
    assert_eq!(cmp::Ordering::Equal, unique.cmp(&unique));
    assert_eq!(cmp::Ordering::Equal, shared.cmp(&shared));
    assert_eq!(Some(cmp::Ordering::Equal), unique.partial_cmp(&shared));
    assert_eq!(Some(cmp::Ordering::Equal), shared.partial_cmp(&unique));
}

#[quickcheck]
#[cfg_attr(miri, ignore)]
fn test_cmp_same_str(s: String) {
    let unique = UniqueString::try_from(s.as_str()).expect("A valid Umbra-style string");
    let shared = SharedString::try_from(s.as_str()).expect("A valid Umbra-style string");
    assert_eq!(Some(cmp::Ordering::Equal), unique.partial_cmp(s.as_str()));
    assert_eq!(Some(cmp::Ordering::Equal), shared.partial_cmp(s.as_str()));
    assert_eq!(Some(cmp::Ordering::Equal), s.as_str().partial_cmp(&unique));
    assert_eq!(Some(cmp::Ordering::Equal), s.as_str().partial_cmp(&shared));
}

#[quickcheck]
#[cfg_attr(miri, ignore)]
fn test_cmp_same_string(s: String) {
    let unique = UniqueString::try_from(s.as_str()).expect("A valid Umbra-style string");
    let shared = SharedString::try_from(s.as_str()).expect("A valid Umbra-style string");
    assert_eq!(Some(cmp::Ordering::Equal), unique.partial_cmp(&s));
    assert_eq!(Some(cmp::Ordering::Equal), shared.partial_cmp(&s));
    assert_eq!(Some(cmp::Ordering::Equal), s.partial_cmp(&unique));
    assert_eq!(Some(cmp::Ordering::Equal), s.partial_cmp(&shared));
}

#[quickcheck]
#[cfg_attr(miri, ignore)]
fn test_cmp_diff(s1: String, s2: String) {
    let lhs_unique = UniqueString::try_from(s1.as_str()).expect("A valid Umbra-style string");
    let rhs_unique = UniqueString::try_from(s2.as_str()).expect("A valid Umbra-style string");
    let lhs_shared = SharedString::try_from(s1.as_str()).expect("A valid Umbra-style string");
    let rhs_shared = SharedString::try_from(s2.as_str()).expect("A valid Umbra-style string");
    assert_eq!(s1.cmp(&s2), lhs_unique.cmp(&rhs_unique));
    assert_eq!(s1.cmp(&s2), lhs_shared.cmp(&rhs_shared));
    assert_eq!(s1.partial_cmp(&s2), lhs_unique.partial_cmp(&rhs_shared));
    assert_eq!(s1.partial_cmp(&s2), lhs_shared.partial_cmp(&rhs_unique));
}

#[quickcheck]
#[cfg_attr(miri, ignore)]
fn test_cmp_diff_str(s1: String, s2: String) {
    let lhs_unique = UniqueString::try_from(s1.as_str()).expect("A valid Umbra-style string");
    let rhs_unique = UniqueString::try_from(s2.as_str()).expect("A valid Umbra-style string");
    let lhs_shared = SharedString::try_from(s1.as_str()).expect("A valid Umbra-style string");
    let rhs_shared = SharedString::try_from(s2.as_str()).expect("A valid Umbra-style string");
    assert_eq!(s1.partial_cmp(&s2), s1.as_str().partial_cmp(&rhs_unique));
    assert_eq!(s1.partial_cmp(&s2), s1.as_str().partial_cmp(&rhs_shared));
    assert_eq!(s1.partial_cmp(&s2), lhs_unique.partial_cmp(s2.as_str()));
    assert_eq!(s1.partial_cmp(&s2), lhs_shared.partial_cmp(s2.as_str()));
}

#[quickcheck]
#[cfg_attr(miri, ignore)]
fn test_cmp_diff_string(s1: String, s2: String) {
    let lhs_unique = UniqueString::try_from(s1.as_str()).expect("A valid Umbra-style string");
    let rhs_unique = UniqueString::try_from(s2.as_str()).expect("A valid Umbra-style string");
    let lhs_shared = SharedString::try_from(s1.as_str()).expect("A valid Umbra-style string");
    let rhs_shared = SharedString::try_from(s2.as_str()).expect("A valid Umbra-style string");
    assert_eq!(s1.partial_cmp(&s2), s1.partial_cmp(&rhs_unique));
    assert_eq!(s1.partial_cmp(&s2), s1.partial_cmp(&rhs_shared));
    assert_eq!(s1.partial_cmp(&s2), lhs_unique.partial_cmp(&s2));
    assert_eq!(s1.partial_cmp(&s2), lhs_shared.partial_cmp(&s2));
}
