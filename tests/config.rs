use lru_cache_macros::lru_cache;

#[test]
fn ignore_args() {
    #[lru_cache(20)]
    #[lru_config(ignore_args = call_count)]
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