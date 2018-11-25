use lru_cache_macros::lru_cache;
use std::time::Duration;
use expiring_map::ExpiringMap;

#[test]
fn cache_type() {
    use std::f64;

    #[lru_cache(Duration::from_secs(60))]
    #[lru_config(cache_type = ExpiringMap)]
    fn cached_sqrt(x: u64) -> f64 {
        f64::sqrt(x as f64)
    }

    assert_eq!(cached_sqrt(9), f64::sqrt(9.0));
}
