lru-cache-macros
================
[![Build Status](https://travis-ci.org/tylerreisinger/lru-cache-macro.svg?branch=master)](https://travis-ci.org/tylerreisinger/lru-cache-macro)
[![lru-cache-macros on docs.rs][docsrs-image]][docsrs]
[![lru-cache-macros on crates.io][crates-image]][crates]

[docsrs-image]: https://docs.rs/lru-cache-macros/badge.svg
[docsrs]: https://docs.rs/lru-cache-macros
[crates-image]: https://img.shields.io/crates/v/lru-cache-macros.svg
[crates]: https://crates.io/crates/lru-cache-macros/

An attribute procedural macro to automatically cache the result of a function given a set of inputs.

# Example:

```rust
use lru_cache_macros::lru_cache;

#[lru_cache(20)]
fn fib(x: u32) -> u64 {
    println!("{:?}", x);
    if x <= 1 {
        1
    } else {
        fib(x - 1) + fib(x - 2)
    }
}

#[test]
fn test_fib() {
    assert_eq!(fib(19), 6765);
}
```

The above example only calls `fib` twenty times, with the values from 0 to 19. All intermediate
results because of the recursion hit the cache.

# Usage:

Simply place `#[lru_cache([size])]` above your function. The function must obey a few properties
to use lru_cache:

* All arguments and return values must implement `Clone`.
* The function may not take `self` in any form.

The macro will use the LruCache at `::lru_cache::LruCache`. This may be made configurable in the future.

The `LruCache` type used must accept two generic parameters `<Args, Return>` and must support methods
`get_mut(&K)` and `insert(K, V)`. The `lru-cache` crate meets these requirements.

Currently, this crate only works on nightly rust. However, once the 2018 edition stabilizes as well as the
procedural macro diagnostic interface, it should be able to run on stable.

# Details

The created cache resides in thread-local storage so that multiple threads may simultaneously call
the decorated function, but will not share cached results with each other.

The above example will generate the following code:

```rust
fn __lru_base_fib(x: u32) -> u64 {
    if x <= 1 { 1 } else { fib(x - 1) + fib(x - 2) }
}
fn fib(x: u32) -> u64 {
    use std::cell::UnsafeCell;
    use std::thread_local;

     thread_local!(
          static cache: UnsafeCell<::lru_cache::LruCache<(u32,), u64>> =
              UnsafeCell::new(::lru_cache::LruCache::new(20usize));
     );

    cache.with(|c|
        {
            let mut cache_ref = unsafe { &mut *c.get() };
            let cloned_args = (x.clone(),);
            let stored_result = cache_ref.get_mut(&cloned_args);
            if let Some(stored_result) = stored_result {
                stored_result.clone()
            } else {
                let ret = __lru_base_fib(x);
                cache_ref.insert(cloned_args, ret);
                ret
            }
        })
}
```

