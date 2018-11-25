use cache_macro::cache;
use std::time::Duration;
use expiring_map::ExpiringMap;
use std::hash::Hash;

#[test]
fn cache_type() {
    use std::f64;

    #[cache(ExpiringMap : ExpiringMap::new(Duration::from_secs(60)))]
    fn cached_sqrt(x: u64) -> f64 {
        f64::sqrt(x as f64)
    }

    assert_eq!(cached_sqrt(9), f64::sqrt(9.0));
}

fn custom_create_cache_method<K, V>(duration: Duration, _extra_arg: u32) -> ExpiringMap<K, V>
    where K: Eq + Hash
{
    ExpiringMap::new(duration)
}

#[test]
fn non_standard_cache_creation() {
    // this tests support for caches which do not use a `new` method,
    //      and/or whose creation function uses more than 1 argument

    use std::f64;

    #[cache(ExpiringMap : custom_create_cache_method(Duration::from_secs(60), 1))]
    fn cached_sqrt(x: u64) -> f64 {
        f64::sqrt(x as f64)
    }

    assert_eq!(cached_sqrt(9), f64::sqrt(9.0));
}
