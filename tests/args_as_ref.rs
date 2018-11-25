use lru_cache_macros::cache;
use lru_cache::LruCache;

#[test]
fn args_as_ref() {
    #[cache(LruCache : LruCache::new(20))]
    fn fib(x: &u32) -> u64 {
        println!("{:?}", x);
        if *x <= 1 {
            1
        } else {
            fib(&(x - 1)) + fib(&(x - 2))
        }
    }

    assert_eq!(fib(&19), 6765);
}

