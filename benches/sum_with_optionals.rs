use criterion::{black_box, criterion_group, criterion_main, Criterion};
use hvec::{hvec, HVec};

#[derive(Clone)]
struct BigStruct {
    number: f32,
    extra: Option<Extra>,
}

#[derive(Clone)]
struct BoxStruct {
    number: f32,
    extra: Option<Box<Extra>>,
}

#[derive(Clone)]
struct BareStruct {
    number: f32,
    has_extra: bool,
}

#[derive(Clone)]
struct Extra {
    array: [f32; 32],
}

fn sum_big(data: Vec<BigStruct>) -> f32 {
    let mut total = 0.;
    for item in data {
        total += item.number;
        if let Some(extra) = &item.extra {
            total += extra.array.iter().sum::<f32>();
        }
    }
    total
}

fn sum_box(data: Vec<BoxStruct>) -> f32 {
    let mut total = 0.;
    for item in data {
        total += item.number;
        if let Some(extra) = &item.extra {
            total += extra.array.iter().sum::<f32>();
        }
    }
    total
}

fn sum_bare(data: HVec) -> f32 {
    let mut total = 0.;
    let mut iter = data.into_iter();
    while let Some(item) = iter.next::<BareStruct>() {
        total += item.number;
        if item.has_extra {
            let extra = iter.next::<Extra>().unwrap();
            total += extra.array.iter().sum::<f32>();
        }
    }
    total
}

fn generate_data(count: usize, phase: usize) -> Vec<(f32, Option<Extra>)> {
    let mut ns = 0..;
    let mut base = Vec::with_capacity(count);
    for i in 0..count {
        let number = ns.next().unwrap() as f32;
        let mut extra = None;
        if (i % phase) == 0 {
            let mut array = [0.; 32];
            for j in 0..32 {
                array[j] = ns.next().unwrap() as f32;
            }
            extra = Some(Extra { array });
        }
        base.push((number, extra));
    }
    base
}

fn big_benchmark(c: &mut Criterion) {
    let data: Vec<BigStruct> = generate_data(1000, 7)
        .into_iter()
        .map(|(number, extra)| BigStruct { number, extra })
        .collect();
    c.bench_function("big structs (vec)", |b| {
        b.iter(|| sum_big(black_box(data.clone())))
    });
}

fn box_benchmark(c: &mut Criterion) {
    let data: Vec<BoxStruct> = generate_data(1000, 7)
        .into_iter()
        .map(|(number, extra)| BoxStruct {
            number,
            extra: extra.map(|x| Box::new(x)),
        })
        .collect();
    c.bench_function("boxed structs (vec)", |b| {
        b.iter(|| sum_box(black_box(data.clone())))
    });
}

fn bare_benchmark(c: &mut Criterion) {
    let mut data = hvec![];
    for (number, extra) in generate_data(1000, 7) {
        data.push(BareStruct {
            number,
            has_extra: extra.is_some(),
        });
        if let Some(extra) = extra {
            data.push(extra);
        }
    }
    c.bench_function("bare structs (hvec)", |b| {
        b.iter(|| sum_bare(black_box(data.clone())))
    });
}

criterion_group!(benches, big_benchmark, box_benchmark, bare_benchmark);
criterion_main!(benches);
