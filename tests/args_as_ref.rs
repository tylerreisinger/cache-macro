#[test]
fn args_as_ref() {
    use lru_cache_macros::lru_cache;

    #[lru_cache(20)]
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

