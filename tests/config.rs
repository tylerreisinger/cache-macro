use lru_cache_macros::lru_cache as cache;
use lru_cache::LruCache;

use std::thread;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time;

#[test]
fn thread_local_ignore_args() {
    #[cache(LruCache : LruCache::new(20))]
    #[cache_cfg(ignore_args = call_count)]
    #[cache_cfg(thread_local)]
    fn fib(x: u32, call_count: &mut u32) -> u64 {
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
}

#[test]
fn multithreaded() {
    static CALL_COUNT: AtomicUsize = AtomicUsize::new(0);

    #[cache(LruCache : LruCache::new(20))]
    fn fib(x: u32) -> u64 {
        CALL_COUNT.fetch_add(1, Ordering::SeqCst);
        if x <= 1 {
            1
        } else {
            fib(x - 1) + fib(x - 2)
        }
    }

    let t1 = thread::spawn( || {
        assert_eq!(fib(39), 102_334_155);
    });

    let ten_millis = time::Duration::from_millis(10);
    thread::sleep(ten_millis);

    let t2 = thread::spawn( || {
        assert_eq!(fib(39), 102_334_155);
    });

    t1.join().unwrap();
    t2.join().unwrap();

    // threads should share a cache, so total runs should be less than 40 * 2
    assert!(CALL_COUNT.load(Ordering::SeqCst) < 80);
}
