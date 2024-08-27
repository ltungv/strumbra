use strumbra::{SharedString, UniqueString};

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use rand::Rng as _;

const INPUT_LENGTHS: [usize; 6] = [4, 8, 12, 16, 32, 64];

fn cmp_random(c: &mut Criterion) {
    let mut group = c.benchmark_group("cmp-random");
    for len in INPUT_LENGTHS {
        group.bench_with_input(BenchmarkId::new("String", len), &len, |b, &len| {
            b.iter_batched_ref(
                || (random_string(len), random_string(len)),
                |(a, b)| a.cmp(&b),
                criterion::BatchSize::SmallInput,
            )
        });
        group.bench_with_input(BenchmarkId::new("SharedString", len), &len, |b, &len| {
            b.iter_batched_ref(
                || {
                    (
                        SharedString::try_from(random_string(len)).unwrap(),
                        SharedString::try_from(random_string(len)).unwrap(),
                    )
                },
                |(a, b)| a.cmp(&b),
                criterion::BatchSize::SmallInput,
            )
        });
        group.bench_with_input(BenchmarkId::new("UniqueString", len), &len, |b, &len| {
            b.iter_batched_ref(
                || {
                    (
                        UniqueString::try_from(random_string(len)).unwrap(),
                        UniqueString::try_from(random_string(len)).unwrap(),
                    )
                },
                |(a, b)| a.cmp(&b),
                criterion::BatchSize::SmallInput,
            )
        });
    }
}

fn cmp_same(c: &mut Criterion) {
    let mut group = c.benchmark_group("cmp-same");
    for len in INPUT_LENGTHS {
        group.bench_with_input(BenchmarkId::new("String", len), &len, |b, &len| {
            b.iter_batched_ref(
                || {
                    let s = random_string(len);
                    (s.clone(), s)
                },
                |(a, b)| a.cmp(&b),
                criterion::BatchSize::SmallInput,
            )
        });
        group.bench_with_input(BenchmarkId::new("SharedString", len), &len, |b, &len| {
            b.iter_batched_ref(
                || {
                    let s = random_string(len);
                    (
                        SharedString::try_from(s.as_str()).unwrap(),
                        SharedString::try_from(s.as_str()).unwrap(),
                    )
                },
                |(a, b)| a.cmp(&b),
                criterion::BatchSize::SmallInput,
            )
        });
        group.bench_with_input(BenchmarkId::new("UniqueString", len), &len, |b, &len| {
            b.iter_batched_ref(
                || {
                    let s = random_string(len);
                    (
                        UniqueString::try_from(s.as_str()).unwrap(),
                        UniqueString::try_from(s.as_str()).unwrap(),
                    )
                },
                |(a, b)| a.cmp(&b),
                criterion::BatchSize::SmallInput,
            )
        });
    }
}

fn eq_random(c: &mut Criterion) {
    let mut group = c.benchmark_group("eq-random");
    for len in INPUT_LENGTHS {
        group.bench_with_input(BenchmarkId::new("String", len), &len, |b, &len| {
            b.iter_batched_ref(
                || (random_string(len), random_string(len)),
                |(a, b)| a.eq(&b),
                criterion::BatchSize::SmallInput,
            )
        });
        group.bench_with_input(BenchmarkId::new("SharedString", len), &len, |b, &len| {
            b.iter_batched_ref(
                || {
                    (
                        SharedString::try_from(random_string(len)).unwrap(),
                        SharedString::try_from(random_string(len)).unwrap(),
                    )
                },
                |(a, b)| a.eq(&b),
                criterion::BatchSize::SmallInput,
            )
        });
        group.bench_with_input(BenchmarkId::new("UniqueString", len), &len, |b, &len| {
            b.iter_batched_ref(
                || {
                    (
                        UniqueString::try_from(random_string(len)).unwrap(),
                        UniqueString::try_from(random_string(len)).unwrap(),
                    )
                },
                |(a, b)| a.eq(&b),
                criterion::BatchSize::SmallInput,
            )
        });
    }
}

fn eq_same(c: &mut Criterion) {
    let mut group = c.benchmark_group("eq-same");
    for len in INPUT_LENGTHS {
        group.bench_with_input(BenchmarkId::new("String", len), &len, |b, &len| {
            b.iter_batched_ref(
                || {
                    let s = random_string(len);
                    (s.clone(), s)
                },
                |(a, b)| a.eq(&b),
                criterion::BatchSize::SmallInput,
            )
        });
        group.bench_with_input(BenchmarkId::new("SharedString", len), &len, |b, &len| {
            b.iter_batched_ref(
                || {
                    let s = random_string(len);
                    (
                        SharedString::try_from(s.as_str()).unwrap(),
                        SharedString::try_from(s.as_str()).unwrap(),
                    )
                },
                |(a, b)| a.eq(&b),
                criterion::BatchSize::SmallInput,
            )
        });
        group.bench_with_input(BenchmarkId::new("UniqueString", len), &len, |b, &len| {
            b.iter_batched_ref(
                || {
                    let s = random_string(len);
                    (
                        UniqueString::try_from(s.as_str()).unwrap(),
                        UniqueString::try_from(s.as_str()).unwrap(),
                    )
                },
                |(a, b)| a.eq(&b),
                criterion::BatchSize::SmallInput,
            )
        });
    }
}

fn random_string(len: usize) -> String {
    let bytes = rand::thread_rng()
        .sample_iter(rand::distributions::Alphanumeric)
        .take(len)
        .collect::<Vec<_>>();

    String::from_utf8(bytes).unwrap()
}

criterion_group!(benches, cmp_random, cmp_same, eq_random, eq_same);
criterion_main!(benches);
