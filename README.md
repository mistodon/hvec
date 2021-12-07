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
