use std::{cmp, thread};

use quickcheck_macros::quickcheck;
use strumbra::{SharedString, UniqueString};

#[test]
fn size_of() {
    assert_eq!(16, std::mem::size_of::<UniqueString>());
    assert_eq!(16, std::mem::size_of::<SharedString>());
}

#[test]
fn construct_inlined() {
    let unique = UniqueString::try_from("hello world").expect("A valid Umbra-style string");
    let shared = SharedString::try_from("hello world").expect("A valid Umbra-style string");
    assert_eq!("hello world", unique.as_ref());
    assert_eq!("hello world", shared.as_ref());
}

#[test]
fn construct_allocated() {
    let unique =
        UniqueString::try_from("Good Morning, Vietnam").expect("A valid Umbra-style string");
    let shared =
        SharedString::try_from("Good Morning, Vietnam").expect("A valid Umbra-style string");
    assert_eq!("Good Morning, Vietnam", unique.as_ref());
    assert_eq!("Good Morning, Vietnam", shared.as_ref());
}

#[test]
fn move_across_threads_inlined() {
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
fn move_across_threads_allocated() {
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

#[test]
fn eq_string_different_length_with_null_byte() {
    let assert = |lhs: &str, rhs: &str| {
        let unique_lhs = UniqueString::try_from(lhs).expect("A valid Umbra-style string");
        let unique_rhs = UniqueString::try_from(rhs).expect("A valid Umbra-style string");
        let shared_lhs = SharedString::try_from(lhs).expect("A valid Umbra-style string");
        let shared_rhs = SharedString::try_from(rhs).expect("A valid Umbra-style string");
        assert_ne!(unique_lhs, unique_rhs);
        assert_ne!(unique_lhs, shared_rhs);
        assert_ne!(shared_lhs, shared_rhs);
        assert_ne!(shared_lhs, unique_rhs);
    };
    assert("abc", "abc\0");
    assert("abc\0", "abc");
    assert("abcdefghijk", "abcdefghijk\0");
    assert("abcdefghijk\0", "abcdefghijk");
}

#[test]
fn cmp_string_different_length_with_null_byte() {
    let assert = |lhs: &str, rhs: &str| {
        let unique_lhs = UniqueString::try_from(lhs).expect("A valid Umbra-style string");
        let unique_rhs = UniqueString::try_from(rhs).expect("A valid Umbra-style string");
        let shared_lhs = SharedString::try_from(lhs).expect("A valid Umbra-style string");
        let shared_rhs = SharedString::try_from(rhs).expect("A valid Umbra-style string");
        assert_eq!(Ord::cmp(lhs, rhs), Ord::cmp(&unique_lhs, &unique_rhs));
        assert_eq!(
            PartialOrd::partial_cmp(lhs, rhs),
            PartialOrd::partial_cmp(&unique_lhs, &shared_rhs)
        );
        assert_eq!(Ord::cmp(lhs, rhs), Ord::cmp(&shared_lhs, &shared_rhs));
        assert_eq!(
            PartialOrd::partial_cmp(lhs, rhs),
            PartialOrd::partial_cmp(&shared_lhs, &unique_rhs)
        );
    };
    assert("abc", "abc\0");
    assert("abc\0", "abc");
    assert("abcdefghijk", "abcdefghijk\0");
    assert("abcdefghijk\0", "abcdefghijk");
}

#[quickcheck]
#[cfg_attr(miri, ignore)]
#[allow(clippy::needless_pass_by_value)]
fn format_debug(s: String) {
    let expected = format!("{s:?}");
    let unique = UniqueString::try_from(s.as_str()).expect("A valid Umbra-style string");
    let shared = SharedString::try_from(s.as_str()).expect("A valid Umbra-style string");
    assert_eq!(expected, format!("{unique:?}"));
    assert_eq!(expected, format!("{shared:?}"));
}

#[quickcheck]
#[cfg_attr(miri, ignore)]
#[allow(clippy::needless_pass_by_value)]
fn format_display(s: String) {
    let unique = UniqueString::try_from(s.as_str()).expect("A valid Umbra-style string");
    let shared = SharedString::try_from(s.as_str()).expect("A valid Umbra-style string");
    assert_eq!(s, format!("{unique}"));
    assert_eq!(s, format!("{shared}"));
}

#[quickcheck]
#[cfg_attr(miri, ignore)]
#[allow(clippy::needless_pass_by_value)]
fn eq(s: String) {
    let unique = UniqueString::try_from(s.as_str()).expect("A valid Umbra-style string");
    let shared = SharedString::try_from(s.as_str()).expect("A valid Umbra-style string");
    assert_eq!(unique, unique);
    assert_eq!(unique, shared);
    assert_eq!(shared, unique);
    assert_eq!(shared, shared);
}

#[quickcheck]
#[cfg_attr(miri, ignore)]
#[allow(clippy::needless_pass_by_value)]
fn eq_str(s: String) {
    let unique = UniqueString::try_from(s.as_str()).expect("A valid Umbra-style string");
    let shared = SharedString::try_from(s.as_str()).expect("A valid Umbra-style string");
    assert_eq!(s.as_str(), &unique);
    assert_eq!(s.as_str(), &shared);
}

#[quickcheck]
#[cfg_attr(miri, ignore)]
#[allow(clippy::needless_pass_by_value)]
fn eq_string(s: String) {
    let unique = UniqueString::try_from(s.as_str()).expect("A valid Umbra-style string");
    let shared = SharedString::try_from(s.as_str()).expect("A valid Umbra-style string");
    assert_eq!(s, unique);
    assert_eq!(s, shared);
}

#[quickcheck]
#[cfg_attr(miri, ignore)]
#[allow(clippy::needless_pass_by_value)]
fn ne(s1: String, s2: String) {
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
#[allow(clippy::needless_pass_by_value)]
fn ne_str(s1: String, s2: String) {
    let lhs_unique = UniqueString::try_from(s1.as_str()).expect("A valid Umbra-style string");
    let rhs_unique = UniqueString::try_from(s2.as_str()).expect("A valid Umbra-style string");
    let lhs_shared = SharedString::try_from(s1.as_str()).expect("A valid Umbra-style string");
    let rhs_shared = SharedString::try_from(s2.as_str()).expect("A valid Umbra-style string");
    assert_ne!(s1.as_str(), &rhs_unique);
    assert_ne!(s1.as_str(), &rhs_shared);
    assert_ne!(&lhs_unique, s2.as_str());
    assert_ne!(&lhs_shared, s2.as_str());
}

#[quickcheck]
#[cfg_attr(miri, ignore)]
#[allow(clippy::needless_pass_by_value)]
fn ne_string(s1: String, s2: String) {
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
#[allow(clippy::needless_pass_by_value)]
fn cmp_same(s: String) {
    let unique = UniqueString::try_from(s.as_str()).expect("A valid Umbra-style string");
    let shared = SharedString::try_from(s.as_str()).expect("A valid Umbra-style string");
    assert_eq!(cmp::Ordering::Equal, unique.cmp(&unique));
    assert_eq!(cmp::Ordering::Equal, shared.cmp(&shared));
    assert_eq!(Some(cmp::Ordering::Equal), unique.partial_cmp(&shared));
    assert_eq!(Some(cmp::Ordering::Equal), shared.partial_cmp(&unique));
}

#[quickcheck]
#[cfg_attr(miri, ignore)]
#[allow(clippy::needless_pass_by_value)]
fn cmp_same_str(s: String) {
    let unique = UniqueString::try_from(s.as_str()).expect("A valid Umbra-style string");
    let shared = SharedString::try_from(s.as_str()).expect("A valid Umbra-style string");
    assert_eq!(Some(cmp::Ordering::Equal), unique.partial_cmp(s.as_str()));
    assert_eq!(Some(cmp::Ordering::Equal), shared.partial_cmp(s.as_str()));
    assert_eq!(Some(cmp::Ordering::Equal), s.as_str().partial_cmp(&unique));
    assert_eq!(Some(cmp::Ordering::Equal), s.as_str().partial_cmp(&shared));
}

#[quickcheck]
#[cfg_attr(miri, ignore)]
#[allow(clippy::needless_pass_by_value)]
fn cmp_same_string(s: String) {
    let unique = UniqueString::try_from(s.as_str()).expect("A valid Umbra-style string");
    let shared = SharedString::try_from(s.as_str()).expect("A valid Umbra-style string");
    assert_eq!(Some(cmp::Ordering::Equal), unique.partial_cmp(&s));
    assert_eq!(Some(cmp::Ordering::Equal), shared.partial_cmp(&s));
    assert_eq!(Some(cmp::Ordering::Equal), s.partial_cmp(&unique));
    assert_eq!(Some(cmp::Ordering::Equal), s.partial_cmp(&shared));
}

#[quickcheck]
#[cfg_attr(miri, ignore)]
#[allow(clippy::needless_pass_by_value)]
fn cmp_diff(s1: String, s2: String) {
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
#[allow(clippy::needless_pass_by_value)]
fn cmp_diff_str(s1: String, s2: String) {
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
#[allow(clippy::needless_pass_by_value)]
fn cmp_diff_string(s1: String, s2: String) {
    let lhs_unique = UniqueString::try_from(s1.as_str()).expect("A valid Umbra-style string");
    let rhs_unique = UniqueString::try_from(s2.as_str()).expect("A valid Umbra-style string");
    let lhs_shared = SharedString::try_from(s1.as_str()).expect("A valid Umbra-style string");
    let rhs_shared = SharedString::try_from(s2.as_str()).expect("A valid Umbra-style string");
    assert_eq!(s1.partial_cmp(&s2), s1.partial_cmp(&rhs_unique));
    assert_eq!(s1.partial_cmp(&s2), s1.partial_cmp(&rhs_shared));
    assert_eq!(s1.partial_cmp(&s2), lhs_unique.partial_cmp(&s2));
    assert_eq!(s1.partial_cmp(&s2), lhs_shared.partial_cmp(&s2));
}
