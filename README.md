hvec
===

[![Crates.io](https://img.shields.io/crates/v/hvec.svg)](https://crates.io/crates/hvec)
[![Docs.rs](https://docs.rs/hvec/badge.svg)](https://docs.rs/hvec)

In memory of Anna Harren, who coined the term [turbofish](https://turbo.fish/) - which you'll see a lot of if you use this crate.

The main purpose of this crate is the `HarrenVec` type - a `Vec`-like data structure that can store items of different types and sizes from each other.

## Usage

```rust
use hvec::hvec;

// Make a list that can contain any type
let list = hvec![
    1_usize,
    2_usize,
    999_usize,
    "Wow, big number!".to_string(),
    3_usize,
];

// Make an iterator (unfortunately can't use `for` loops)
let mut iter = list.into_iter();

// Use `next` with the turbofish to step through elements of different types
let mut total = 0;
while let Some(number) = iter.next::<usize>() {
    if number > 100 {
        let comment = iter.next::<String>().unwrap();
        println!("{}", comment); // Wow, big number!
    }
    total += number;
}
assert_eq!(total, 1005);
```

## Iteration benchmark

The `sum_with_optionals` benchmark in this repo measures the relative time taken to iterate over a collection of small pieces of data with larger pieces of data sparsely distributed within the same collection.

This is accomplished three ways:

1. Including the larger data in an Option (so every struct is large, but more cache-friendly)
2. Including the larger data in a Box (so it is stored on the heap and the structs being iterated over stay small)
3. Including both large and small structs within the same `HVec` (so there is no indirection and minimal storage overhead)

### Data types

```rust
// 128 bytes
struct Extra {
    array: [f32; 32],
}

// 136 bytes (including the tag for the Option enum)
struct BigStruct {
    number: f32,
    extra: Option<Extra>,
}

// 12 bytes on the stack (plus 128 on the heap)
struct BoxStruct {
    number: f32,
    extra: Option<Box<Extra>>,
}

// 8 bytes, bool indicates whether an `Extra` will be packed next to it
struct BareStruct {
    number: f32,
    has_extra: bool,
}
```

The `BigStruct` and `BoxStruct` structures encode within the struct whether the `Extra` data is included, thus either inflating the size of the struct, or adding a layer of indirection to the heap.

The `BareStruct` just has a flag that indicates whether the `Extra` data will follow it in-band.

### Timings

| Benchmark | When ~50% have Extra | When ~10% have Extra | When ~1% have Extra |
| - | - | - | - |
| BigStruct, 1000x | 38.910µs | 24.111µs | 19.717µs |
| BoxStruct, 1000x | 49.197µs | 15.292µs | **2.6134µs** |
| HVec, 1000x | **27.757µs** | **11.132µs** | 5.6643µs |
| - | - | - | - |
| BigStruct, 4000x | 156.29µs | 95.310µs | 79.063µs |
| BoxStruct, 4000x | 220.69µs | 62.703µs | **10.651µs** |
| HVec, 4000x | **114.26µs** | **45.898µs** | 22.677µs |
| - | - | - | - |
| BigStruct, 16000x | 676.91µs | 399.65µs | 339.60µs |
| BoxStruct, 16000x | 928.10µs | 266.41µs | **41.443µs** |
| HVec, 16000x | **460.43µs** | **181.65µs** | 90.787µs |

If you were to judge by these benchmarks: unless the larger data included in your collection is very rare, `HVec` can be a more time and space efficient way to store and iterate over it.
