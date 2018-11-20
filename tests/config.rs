use lru_cache_macros::lru_cache;
use std::thread;
use std::sync::atomic::{AtomicUsize, Ordering};

static CALL_COUNT: AtomicUsize = AtomicUsize::new(0);

#[test]
fn ignore_args() {
    #[lru_cache(20)]
    #[lru_config(ignore_args = call_count)]
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

    let t2 = thread::spawn( || {
        assert_eq!(fib(39), 102_334_155);
    });

    let t3 = thread::spawn( || {
        assert_eq!(fib(39), 102_334_155);
    });

    t1.join().unwrap();
    t2.join().unwrap();
    t3.join().unwrap();

    // threads should share a cache, so total runs should be less than 40 * 3
    assert!(CALL_COUNT.load(Ordering::SeqCst) < 120);
}
