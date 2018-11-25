cache-macro
================
[![Build Status](https://travis-ci.org/tylerreisinger/cache-macro.svg?branch=master)](https://travis-ci.org/tylerreisinger/cache_macro)
[![cache-macro on docs.rs][docsrs-image]][docsrs]
[![cache-macro on crates.io][crates-image]][crates]

[docsrs-image]: https://docs.rs/cache-macro/badge.svg
[docsrs]: https://docs.rs/cache-macro
[crates-image]: https://img.shields.io/crates/v/cache-macro.svg
[crates]: https://crates.io/crates/cache-macro/

A procedural macro to automatically cache the result of a function given a set of inputs.

Previously named 'lru-cache-macros', but renamed to reflect the broadening of scope.

# Example:

```rust
use cache_macro::cache;
use lru_cache::LruCache;

#[cache(LruCache : LruCache::new(20))]
fn fib(x: u32) -> u64 {
    println!("{:?}", x);
    if x <= 1 {
        1
    } else {
        fib(x - 1) + fib(x - 2)
    }
}

assert_eq!(fib(19), 6765);
```

The above example only calls `fib` twenty times, with the values from 0 to 19. All intermediate
results because of the recursion hit the cache.

# Usage:

Simply place `#[cache(CacheType : constructor)]` above your function. The function must obey a few properties
to use lru_cache:

* All arguments and return values must implement `Clone`.
* The function may not take `self` in any form.

The `LruCache` type used must accept two generic parameters `<Args, Return>` and must support methods
`get_mut(&K) -> Option<&mut V>` and `insert(K, V)`. The `lru-cache` (for LRU caching)
and `expiring_map` (for time-to-live caching) crates currently meet these requirements.

Currently, this crate only works on nightly rust. However, once the 2018 edition stabilizes as well as the
procedural macro diagnostic interface, it should be able to run on stable.

# Configuration:

The lru_cache macro can be configured by adding additional attributes under `#[cache(...)]`.

All configuration attributes take the form `#[cache_cfg(...)]`. The available attributes are:

* `#[cache_cfg(ignore_args = ...)]`

This allows certain arguments to be ignored for the purposes of caching. That means they are not part of the
hash table key and thus should never influence the output of the function. It can be useful for diagnostic settings,
returning the number of times executed, or other introspection purposes.

`ignore_args` takes a comma-separated list of variable identifiers to ignore.

### Example:
```rust
use cache_macro::cache;
use lru_cache::LruCache;
#[cache(LruCache : LruCache::new(20))]
#[cache_cfg(ignore_args = call_count)]
fn fib(x: u64, call_count: &mut u32) -> u64 {
    *call_count += 1;
    if x <= 1 {
        1
    } else {
        fib(x - 1, call_count) + fib(x - 2, call_count)
    }
}

let mut call_count = 0;
assert_eq!(fib(39, &mut call_count), 102_334_155);
assert_eq!(call_count, 40);
```

The `call_count` argument can vary, caching is only done based on `x`.

* `#[cache_cfg(thread_local)]`

Store the cache in thread-local storage instead of global static storage. This avoids the overhead of Mutex locking,
but each thread will be given its own cache, and all caching will not affect any other thread.

Expanding on the first example:

```rust
use cache_macro::cache;
use lru_cache::LruCache;

#[cache(LruCache : LruCache::new(20))]
#[cache_cfg(thread_local)]
fn fib(x: u32) -> u64 {
    println!("{:?}", x);
    if x <= 1 {
        1
    } else {
        fib(x - 1) + fib(x - 2)
    }
}

assert_eq!(fib(19), 6765);
```

# Details
The created cache is stored as a static variable protected by a mutex unless the `#[cache_cfg(thread_local)]`
configuration is added.

With the default settings, the fibonacci example will generate the following code:

```rust
fn __lru_base_fib(x: u32) -> u64 {
    if x <= 1 { 1 } else { fib(x - 1) + fib(x - 2) }
}
fn fib(x: u32) -> u64 {
    use lazy_static::lazy_static;
    use std::sync::Mutex;

    lazy_static! {
        static ref cache: Mutex<::lru_cache::LruCache<(u32,), u64>> =
            Mutex::new(::lru_cache::LruCache::new(20usize));
    }

    let cloned_args = (x.clone(),);
    let mut cache_unlocked = cache.lock().unwrap();
    let stored_result = cache_unlocked.get_mut(&cloned_args);
    if let Some(stored_result) = stored_result {
        return stored_result.clone();
    };
    drop(cache_unlocked);
    let ret = __lru_base_fib(x);
    let mut cache_unlocked = cache.lock().unwrap();
    cache_unlocked.insert(cloned_args, ret.clone());
    ret
}

```

Whereas, if you use the `#[lru_config(thread_local)]` the generated code will look like:


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
                cache_ref.insert(cloned_args, ret.clone());
                ret
            }
        })
}
```
