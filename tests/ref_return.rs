use lru_cache_macros::lru_cache;

#[test]
fn cache_vec() {
    #[lru_cache(20)]
    #[lru_config(ignore_args = call_count)]
    fn get_vec(x: u32, call_count: &mut u32) -> &'static Vec<u32> {
        *call_count += 1;
        (0..x).collect::<Vec<_>>()
    }

    let mut call_count = 0;
    assert_eq!(get_vec(5, &mut call_count).clone(), vec![0, 1, 2, 3, 4]);
    assert_eq!(call_count, 1);
    assert_eq!(get_vec(5, &mut call_count).clone(), vec![0, 1, 2, 3, 4]);
    assert_eq!(call_count, 1);

}