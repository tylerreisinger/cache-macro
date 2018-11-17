lru-cache-macros
================

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
* Reference arguments are not supported.

The macro will use the LruCache at `::lru_cache::LruCache`. This may be made configurable in the future.

The `LruCache` type used must accept two generic parameters `<Args, Return>` and must support methods
`get_mut(&K)` and `insert(K, V)`. The `lru-cache` crate meets these requirements.

# Details

The above example will generate the following code:

```rust
fn __lru_base_fib(x: u32) -> u64 {
    if x <= 1 { 1 } else { fib(x - 1) + fib(x - 2) }
}
fn fib(x: u32) -> u64 {
    static mut cache: Option<::lru_cache::LruCache<(u32,), u64>> = None;
    unsafe {
        if cache.is_none() {
            cache = Some(::lru_cache::LruCache::new(20usize));
        }
    }
    let mut cache_ref = unsafe { cache.as_mut().unwrap() };
    let cloned_args = (x.clone(),);
    let stored_result = cache_ref.get_mut(&cloned_args);
    if let Some(stored_result) = stored_result {
        *stored_result
    } else {
        let ret = __lru_base_fib(x);
        cache_ref.insert(cloned_args, ret);
        ret
    }
}
```

Note that the current implementation is not thread safe. A mutex may be supported in the future.
