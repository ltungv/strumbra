macro_rules! testgen {
    ($mod:ident, $N:expr) => {
        mod $mod {
            use std::{cmp, thread};

            use quickcheck_macros::quickcheck;

            type BoxString = strumbra::BoxString<$N>;
            type ArcString = strumbra::ArcString<$N>;
            type RcString = strumbra::RcString<$N>;

            #[test]
            fn size_of() {
                let expected_size = 4 + $N + std::mem::size_of::<usize>();
                assert_eq!(expected_size, std::mem::size_of::<BoxString>());
                assert_eq!(expected_size, std::mem::size_of::<ArcString>());
                assert_eq!(expected_size, std::mem::size_of::<RcString>());
            }

            #[test]
            fn construct_inlined() {
                let inlined_length = $N + std::mem::size_of::<usize>();
                let expected = "0".repeat(inlined_length);
                let boxed =
                    BoxString::try_from(expected.as_str()).expect("A valid Umbra-style string");
                let arc =
                    ArcString::try_from(expected.as_str()).expect("A valid Umbra-style string");
                let rc = RcString::try_from(expected.as_str()).expect("A valid Umbra-style string");

                assert_eq!(expected, boxed.as_ref());
                assert_eq!(expected, arc.as_ref());
                assert_eq!(expected, rc.as_ref());
            }

            #[test]
            fn construct_allocated() {
                let alloc_length = ($N + std::mem::size_of::<usize>()) * 2;
                let expected = "0".repeat(alloc_length);
                let boxed =
                    BoxString::try_from(expected.as_str()).expect("A valid Umbra-style string");
                let arc =
                    ArcString::try_from(expected.as_str()).expect("A valid Umbra-style string");
                let rc = RcString::try_from(expected.as_str()).expect("A valid Umbra-style string");

                assert_eq!(expected, boxed.as_ref());
                assert_eq!(expected, arc.as_ref());
                assert_eq!(expected, rc.as_ref());
            }

            #[test]
            fn move_across_threads_inlined() {
                let inlined_length = $N + std::mem::size_of::<usize>();
                let expected = "0".repeat(inlined_length);
                let boxed =
                    BoxString::try_from(expected.as_str()).expect("A valid Umbra-style string");
                let arc =
                    ArcString::try_from(expected.as_str()).expect("A valid Umbra-style string");

                let handles: Vec<_> = (0..8)
                    .map(|_| {
                        let cloned0 = boxed.clone();
                        let cloned1 = arc.clone();
                        thread::spawn(move || assert_eq!(cloned0, cloned1))
                    })
                    .collect();

                for handle in handles {
                    handle.join().expect("Thread finishes successfully");
                }
            }

            #[test]
            fn move_across_threads_allocated() {
                let alloc_length = ($N + std::mem::size_of::<usize>()) * 2;
                let expected = "0".repeat(alloc_length);
                let boxed =
                    BoxString::try_from(expected.as_str()).expect("A valid Umbra-style string");
                let arc =
                    ArcString::try_from(expected.as_str()).expect("A valid Umbra-style string");

                let handles: Vec<_> = (0..8)
                    .map(|_| {
                        let cloned0 = boxed.clone();
                        let cloned1 = arc.clone();
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
                    let boxed_lhs = BoxString::try_from(lhs).expect("A valid Umbra-style string");
                    let boxed_rhs = BoxString::try_from(rhs).expect("A valid Umbra-style string");
                    let arc_lhs = ArcString::try_from(lhs).expect("A valid Umbra-style string");
                    let arc_rhs = ArcString::try_from(rhs).expect("A valid Umbra-style string");
                    let rc_lhs = RcString::try_from(lhs).expect("A valid Umbra-style string");
                    let rc_rhs = RcString::try_from(rhs).expect("A valid Umbra-style string");

                    assert_ne!(boxed_lhs, boxed_rhs);
                    assert_ne!(boxed_lhs, arc_rhs);
                    assert_ne!(boxed_lhs, rc_rhs);

                    assert_ne!(arc_lhs, arc_rhs);
                    assert_ne!(arc_lhs, rc_rhs);
                    assert_ne!(arc_lhs, boxed_rhs);

                    assert_ne!(rc_lhs, rc_rhs);
                    assert_ne!(rc_lhs, boxed_rhs);
                    assert_ne!(rc_lhs, arc_rhs);
                };

                let inlined_length = $N + std::mem::size_of::<usize>();

                let mut prefix1 = "0".repeat($N - 1);
                let prefix2 = "0".repeat($N - 1);

                let mut inlined1 = "0".repeat(inlined_length - 1);
                let inlined2 = "0".repeat(inlined_length - 1);

                prefix1.push_str("\0");
                inlined1.push_str("\0");

                assert(prefix1.as_str(), prefix2.as_str());
                assert(prefix2.as_str(), prefix1.as_str());
                assert(inlined1.as_str(), inlined2.as_str());
                assert(inlined2.as_str(), inlined1.as_str());
            }

            #[test]
            fn cmp_string_different_length_with_null_byte() {
                let assert = |lhs: &str, rhs: &str| {
                    let boxed_lhs = BoxString::try_from(lhs).expect("A valid Umbra-style string");
                    let boxed_rhs = BoxString::try_from(rhs).expect("A valid Umbra-style string");
                    let arc_lhs = ArcString::try_from(lhs).expect("A valid Umbra-style string");
                    let arc_rhs = ArcString::try_from(rhs).expect("A valid Umbra-style string");
                    let rc_lhs = RcString::try_from(lhs).expect("A valid Umbra-style string");
                    let rc_rhs = RcString::try_from(rhs).expect("A valid Umbra-style string");

                    assert_eq!(Ord::cmp(lhs, rhs), Ord::cmp(&boxed_lhs, &boxed_rhs));
                    assert_eq!(Ord::cmp(lhs, rhs), Ord::cmp(&arc_lhs, &arc_rhs));
                    assert_eq!(Ord::cmp(lhs, rhs), Ord::cmp(&rc_lhs, &rc_rhs));

                    assert_eq!(
                        PartialOrd::partial_cmp(lhs, rhs),
                        PartialOrd::partial_cmp(&boxed_lhs, &arc_rhs)
                    );
                    assert_eq!(
                        PartialOrd::partial_cmp(lhs, rhs),
                        PartialOrd::partial_cmp(&boxed_lhs, &rc_rhs)
                    );

                    assert_eq!(
                        PartialOrd::partial_cmp(lhs, rhs),
                        PartialOrd::partial_cmp(&arc_lhs, &rc_rhs)
                    );
                    assert_eq!(
                        PartialOrd::partial_cmp(lhs, rhs),
                        PartialOrd::partial_cmp(&arc_lhs, &boxed_rhs)
                    );

                    assert_eq!(
                        PartialOrd::partial_cmp(lhs, rhs),
                        PartialOrd::partial_cmp(&rc_lhs, &boxed_rhs)
                    );
                    assert_eq!(
                        PartialOrd::partial_cmp(lhs, rhs),
                        PartialOrd::partial_cmp(&rc_lhs, &arc_rhs)
                    );
                };

                let inlined_length = $N + std::mem::size_of::<usize>();

                let mut prefix1 = "0".repeat($N - 1);
                let prefix2 = "0".repeat($N - 1);

                let mut inlined1 = "0".repeat(inlined_length - 1);
                let inlined2 = "0".repeat(inlined_length - 1);

                prefix1.push_str("\0");
                inlined1.push_str("\0");

                assert(prefix1.as_str(), prefix2.as_str());
                assert(prefix2.as_str(), prefix1.as_str());
                assert(inlined1.as_str(), inlined2.as_str());
                assert(inlined2.as_str(), inlined1.as_str());
            }

            #[quickcheck]
            #[cfg_attr(miri, ignore)]
            #[allow(clippy::needless_pass_by_value)]
            fn format_debug(s: String) {
                let expected = format!("{s:?}");
                let boxed = BoxString::try_from(s.as_str()).expect("A valid Umbra-style string");
                let arc = ArcString::try_from(s.as_str()).expect("A valid Umbra-style string");
                let rc = RcString::try_from(s.as_str()).expect("A valid Umbra-style string");

                assert_eq!(expected, format!("{boxed:?}"));
                assert_eq!(expected, format!("{arc:?}"));
                assert_eq!(expected, format!("{rc:?}"));
            }

            #[quickcheck]
            #[cfg_attr(miri, ignore)]
            #[allow(clippy::needless_pass_by_value)]
            fn format_display(s: String) {
                let boxed = BoxString::try_from(s.as_str()).expect("A valid Umbra-style string");
                let arc = ArcString::try_from(s.as_str()).expect("A valid Umbra-style string");
                let rc = RcString::try_from(s.as_str()).expect("A valid Umbra-style string");

                assert_eq!(s, format!("{boxed}"));
                assert_eq!(s, format!("{arc}"));
                assert_eq!(s, format!("{rc}"));
            }

            #[quickcheck]
            #[cfg_attr(miri, ignore)]
            #[allow(clippy::needless_pass_by_value)]
            fn eq_same(s: String) {
                let boxed = BoxString::try_from(s.as_str()).expect("A valid Umbra-style string");
                let arc = ArcString::try_from(s.as_str()).expect("A valid Umbra-style string");
                let rc = RcString::try_from(s.as_str()).expect("A valid Umbra-style string");

                assert_eq!(boxed, boxed);
                assert_eq!(boxed, arc);
                assert_eq!(boxed, rc);

                assert_eq!(arc, arc);
                assert_eq!(arc, rc);
                assert_eq!(arc, boxed);

                assert_eq!(rc, rc);
                assert_eq!(rc, boxed);
                assert_eq!(rc, arc);
            }

            #[quickcheck]
            #[cfg_attr(miri, ignore)]
            #[allow(clippy::needless_pass_by_value)]
            fn eq_same_str(s: String) {
                let boxed = BoxString::try_from(s.as_str()).expect("A valid Umbra-style string");
                let arc = ArcString::try_from(s.as_str()).expect("A valid Umbra-style string");
                let rc = RcString::try_from(s.as_str()).expect("A valid Umbra-style string");

                assert_eq!(s.as_str(), &boxed);
                assert_eq!(s.as_str(), &arc);
                assert_eq!(s.as_str(), &rc);
            }

            #[quickcheck]
            #[cfg_attr(miri, ignore)]
            #[allow(clippy::needless_pass_by_value)]
            fn eq_same_string(s: String) {
                let boxed = BoxString::try_from(s.as_str()).expect("A valid Umbra-style string");
                let arc = ArcString::try_from(s.as_str()).expect("A valid Umbra-style string");
                let rc = RcString::try_from(s.as_str()).expect("A valid Umbra-style string");

                assert_eq!(s, boxed);
                assert_eq!(s, arc);
                assert_eq!(s, rc);
            }

            #[quickcheck]
            #[cfg_attr(miri, ignore)]
            #[allow(clippy::needless_pass_by_value)]
            fn eq_diff(s1: String, s2: String) {
                let lhs_boxed =
                    BoxString::try_from(s1.as_str()).expect("A valid Umbra-style string");
                let rhs_boxed =
                    BoxString::try_from(s2.as_str()).expect("A valid Umbra-style string");
                let lhs_arc = ArcString::try_from(s1.as_str()).expect("A valid Umbra-style string");
                let rhs_arc = ArcString::try_from(s2.as_str()).expect("A valid Umbra-style string");
                let lhs_rc = RcString::try_from(s1.as_str()).expect("A valid Umbra-style string");
                let rhs_rc = RcString::try_from(s2.as_str()).expect("A valid Umbra-style string");

                assert_eq!(s1.eq(&s2), lhs_boxed.eq(&rhs_boxed));
                assert_eq!(s1.eq(&s2), lhs_boxed.eq(&rhs_arc));
                assert_eq!(s1.eq(&s2), lhs_boxed.eq(&rhs_rc));

                assert_eq!(s1.eq(&s2), lhs_arc.eq(&rhs_arc));
                assert_eq!(s1.eq(&s2), lhs_arc.eq(&rhs_rc));
                assert_eq!(s1.eq(&s2), lhs_arc.eq(&rhs_boxed));

                assert_eq!(s1.eq(&s2), lhs_rc.eq(&rhs_rc));
                assert_eq!(s1.eq(&s2), lhs_rc.eq(&rhs_boxed));
                assert_eq!(s1.eq(&s2), lhs_rc.eq(&rhs_arc));
            }

            #[quickcheck]
            #[cfg_attr(miri, ignore)]
            #[allow(clippy::needless_pass_by_value)]
            fn eq_diff_str(s1: String, s2: String) {
                let lhs_boxed =
                    BoxString::try_from(s1.as_str()).expect("A valid Umbra-style string");
                let rhs_boxed =
                    BoxString::try_from(s2.as_str()).expect("A valid Umbra-style string");
                let lhs_arc = ArcString::try_from(s1.as_str()).expect("A valid Umbra-style string");
                let rhs_arc = ArcString::try_from(s2.as_str()).expect("A valid Umbra-style string");
                let lhs_rc = RcString::try_from(s1.as_str()).expect("A valid Umbra-style string");
                let rhs_rc = RcString::try_from(s2.as_str()).expect("A valid Umbra-style string");

                assert_eq!(s1.eq(&s2), s1.as_str().eq(&rhs_boxed));
                assert_eq!(s1.eq(&s2), s1.as_str().eq(&rhs_arc));
                assert_eq!(s1.eq(&s2), s1.as_str().eq(&rhs_rc));

                assert_eq!(s1.eq(&s2), lhs_boxed.eq(s2.as_str()));
                assert_eq!(s1.eq(&s2), lhs_arc.eq(s2.as_str()));
                assert_eq!(s1.eq(&s2), lhs_rc.eq(s2.as_str()));
            }

            #[quickcheck]
            #[cfg_attr(miri, ignore)]
            #[allow(clippy::needless_pass_by_value)]
            fn eq_diff_string(s1: String, s2: String) {
                let lhs_boxed =
                    BoxString::try_from(s1.as_str()).expect("A valid Umbra-style string");
                let rhs_boxed =
                    BoxString::try_from(s2.as_str()).expect("A valid Umbra-style string");
                let lhs_arc = ArcString::try_from(s1.as_str()).expect("A valid Umbra-style string");
                let rhs_arc = ArcString::try_from(s2.as_str()).expect("A valid Umbra-style string");
                let lhs_rc = RcString::try_from(s1.as_str()).expect("A valid Umbra-style string");
                let rhs_rc = RcString::try_from(s2.as_str()).expect("A valid Umbra-style string");

                assert_eq!(s1.eq(&s2), s1.eq(&rhs_boxed));
                assert_eq!(s1.eq(&s2), s1.eq(&rhs_arc));
                assert_eq!(s1.eq(&s2), s1.eq(&rhs_rc));

                assert_eq!(s1.eq(&s2), lhs_boxed.eq(&s2));
                assert_eq!(s1.eq(&s2), lhs_arc.eq(&s2));
                assert_eq!(s1.eq(&s2), lhs_rc.eq(&s2));
            }

            #[quickcheck]
            #[cfg_attr(miri, ignore)]
            #[allow(clippy::needless_pass_by_value)]
            fn cmp_same(s: String) {
                let boxed = BoxString::try_from(s.as_str()).expect("A valid Umbra-style string");
                let arc = ArcString::try_from(s.as_str()).expect("A valid Umbra-style string");
                let rc = RcString::try_from(s.as_str()).expect("A valid Umbra-style string");

                assert_eq!(cmp::Ordering::Equal, boxed.cmp(&boxed));
                assert_eq!(cmp::Ordering::Equal, arc.cmp(&arc));
                assert_eq!(cmp::Ordering::Equal, rc.cmp(&rc));

                assert_eq!(Some(cmp::Ordering::Equal), boxed.partial_cmp(&arc));
                assert_eq!(Some(cmp::Ordering::Equal), boxed.partial_cmp(&rc));

                assert_eq!(Some(cmp::Ordering::Equal), arc.partial_cmp(&boxed));
                assert_eq!(Some(cmp::Ordering::Equal), arc.partial_cmp(&rc));

                assert_eq!(Some(cmp::Ordering::Equal), rc.partial_cmp(&boxed));
                assert_eq!(Some(cmp::Ordering::Equal), rc.partial_cmp(&arc));
            }

            #[quickcheck]
            #[cfg_attr(miri, ignore)]
            #[allow(clippy::needless_pass_by_value)]
            fn cmp_same_str(s: String) {
                let boxed = BoxString::try_from(s.as_str()).expect("A valid Umbra-style string");
                let arc = ArcString::try_from(s.as_str()).expect("A valid Umbra-style string");
                let rc = RcString::try_from(s.as_str()).expect("A valid Umbra-style string");

                assert_eq!(Some(cmp::Ordering::Equal), boxed.partial_cmp(s.as_str()));
                assert_eq!(Some(cmp::Ordering::Equal), arc.partial_cmp(s.as_str()));
                assert_eq!(Some(cmp::Ordering::Equal), rc.partial_cmp(s.as_str()));

                assert_eq!(Some(cmp::Ordering::Equal), s.as_str().partial_cmp(&boxed));
                assert_eq!(Some(cmp::Ordering::Equal), s.as_str().partial_cmp(&arc));
                assert_eq!(Some(cmp::Ordering::Equal), s.as_str().partial_cmp(&rc));
            }

            #[quickcheck]
            #[cfg_attr(miri, ignore)]
            #[allow(clippy::needless_pass_by_value)]
            fn cmp_same_string(s: String) {
                let boxed = BoxString::try_from(s.as_str()).expect("A valid Umbra-style string");
                let arc = ArcString::try_from(s.as_str()).expect("A valid Umbra-style string");
                let rc = RcString::try_from(s.as_str()).expect("A valid Umbra-style string");

                assert_eq!(Some(cmp::Ordering::Equal), boxed.partial_cmp(&s));
                assert_eq!(Some(cmp::Ordering::Equal), arc.partial_cmp(&s));
                assert_eq!(Some(cmp::Ordering::Equal), rc.partial_cmp(&s));

                assert_eq!(Some(cmp::Ordering::Equal), s.partial_cmp(&boxed));
                assert_eq!(Some(cmp::Ordering::Equal), s.partial_cmp(&arc));
                assert_eq!(Some(cmp::Ordering::Equal), s.partial_cmp(&rc));
            }

            #[quickcheck]
            #[cfg_attr(miri, ignore)]
            #[allow(clippy::needless_pass_by_value)]
            fn cmp_diff(s1: String, s2: String) {
                let lhs_boxed =
                    BoxString::try_from(s1.as_str()).expect("A valid Umbra-style string");
                let rhs_boxed =
                    BoxString::try_from(s2.as_str()).expect("A valid Umbra-style string");
                let lhs_arc = ArcString::try_from(s1.as_str()).expect("A valid Umbra-style string");
                let rhs_arc = ArcString::try_from(s2.as_str()).expect("A valid Umbra-style string");
                let lhs_rc = RcString::try_from(s1.as_str()).expect("A valid Umbra-style string");
                let rhs_rc = RcString::try_from(s2.as_str()).expect("A valid Umbra-style string");

                assert_eq!(s1.cmp(&s2), lhs_boxed.cmp(&rhs_boxed));
                assert_eq!(s1.cmp(&s2), lhs_arc.cmp(&rhs_arc));
                assert_eq!(s1.cmp(&s2), lhs_rc.cmp(&rhs_rc));

                assert_eq!(s1.partial_cmp(&s2), lhs_boxed.partial_cmp(&rhs_arc));
                assert_eq!(s1.partial_cmp(&s2), lhs_boxed.partial_cmp(&rhs_rc));

                assert_eq!(s1.partial_cmp(&s2), lhs_arc.partial_cmp(&rhs_boxed));
                assert_eq!(s1.partial_cmp(&s2), lhs_arc.partial_cmp(&rhs_rc));

                assert_eq!(s1.partial_cmp(&s2), lhs_rc.partial_cmp(&rhs_boxed));
                assert_eq!(s1.partial_cmp(&s2), lhs_rc.partial_cmp(&rhs_arc));
            }

            #[quickcheck]
            #[cfg_attr(miri, ignore)]
            #[allow(clippy::needless_pass_by_value)]
            fn cmp_diff_str(s1: String, s2: String) {
                let lhs_boxed =
                    BoxString::try_from(s1.as_str()).expect("A valid Umbra-style string");
                let rhs_boxed =
                    BoxString::try_from(s2.as_str()).expect("A valid Umbra-style string");
                let lhs_arc = ArcString::try_from(s1.as_str()).expect("A valid Umbra-style string");
                let rhs_arc = ArcString::try_from(s2.as_str()).expect("A valid Umbra-style string");
                let lhs_rc = RcString::try_from(s1.as_str()).expect("A valid Umbra-style string");
                let rhs_rc = RcString::try_from(s2.as_str()).expect("A valid Umbra-style string");

                assert_eq!(s1.partial_cmp(&s2), s1.as_str().partial_cmp(&rhs_boxed));
                assert_eq!(s1.partial_cmp(&s2), s1.as_str().partial_cmp(&rhs_arc));
                assert_eq!(s1.partial_cmp(&s2), s1.as_str().partial_cmp(&rhs_rc));

                assert_eq!(s1.partial_cmp(&s2), lhs_boxed.partial_cmp(s2.as_str()));
                assert_eq!(s1.partial_cmp(&s2), lhs_arc.partial_cmp(s2.as_str()));
                assert_eq!(s1.partial_cmp(&s2), lhs_rc.partial_cmp(s2.as_str()));
            }

            #[quickcheck]
            #[cfg_attr(miri, ignore)]
            #[allow(clippy::needless_pass_by_value)]
            fn cmp_diff_string(s1: String, s2: String) {
                let lhs_boxed =
                    BoxString::try_from(s1.as_str()).expect("A valid Umbra-style string");
                let rhs_boxed =
                    BoxString::try_from(s2.as_str()).expect("A valid Umbra-style string");
                let lhs_arc = ArcString::try_from(s1.as_str()).expect("A valid Umbra-style string");
                let rhs_arc = ArcString::try_from(s2.as_str()).expect("A valid Umbra-style string");
                let lhs_rc = RcString::try_from(s1.as_str()).expect("A valid Umbra-style string");
                let rhs_rc = RcString::try_from(s2.as_str()).expect("A valid Umbra-style string");

                assert_eq!(s1.partial_cmp(&s2), s1.partial_cmp(&rhs_boxed));
                assert_eq!(s1.partial_cmp(&s2), s1.partial_cmp(&rhs_arc));
                assert_eq!(s1.partial_cmp(&s2), s1.partial_cmp(&rhs_rc));

                assert_eq!(s1.partial_cmp(&s2), lhs_boxed.partial_cmp(&s2));
                assert_eq!(s1.partial_cmp(&s2), lhs_arc.partial_cmp(&s2));
                assert_eq!(s1.partial_cmp(&s2), lhs_rc.partial_cmp(&s2));
            }
        }
    };
}

testgen!(prefix4, 4);
testgen!(prefix12, 12);
testgen!(prefix20, 20);
testgen!(prefix28, 28);
