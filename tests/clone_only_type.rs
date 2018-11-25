use cache_macro::cache;
use lru_cache::LruCache;

use std::ops;


#[derive(Clone, Eq, PartialEq, Hash, Debug, Ord, PartialOrd)]
struct NoCopyI32(i32);

impl ops::Add for NoCopyI32 {
    type Output = NoCopyI32;
    fn add(self, rhs: Self) -> Self {
        NoCopyI32(self.0 + rhs.0)
    }
}
impl ops::Sub for NoCopyI32 {
    type Output = NoCopyI32;
    fn sub(self, rhs: Self) -> Self {
        NoCopyI32(self.0 - rhs.0)
    }
}

#[test]
fn clone_only_type() {
    #[cache(LruCache : LruCache::new(20))]
    fn fib(x: NoCopyI32) -> NoCopyI32 {
        if x <= NoCopyI32(1) {
            NoCopyI32(1)
        } else {
            fib(x.clone() - NoCopyI32(1)) + fib(x - NoCopyI32(2))
        }
    }

    assert_eq!(fib(NoCopyI32(19)), NoCopyI32(6765));
}
