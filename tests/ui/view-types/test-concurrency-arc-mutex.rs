//@ check-pass
#![feature(view_types)]
#![allow(unused, incomplete_features)]

// TEST: Concurrency with Arc<Mutex<T>> and View Types
//
// CRITICAL PROPERTY: View-typed methods must work correctly when the struct
// is wrapped in Arc<Mutex<T>> and shared across threads.
//
// This tests the most common Rust concurrency pattern:
// - Arc for shared ownership across threads
// - Mutex for interior mutability
// - View types for fine-grained field access
//
// VERIFICATION:
// 1. View-typed methods work through Mutex lock guards
// 2. Send/Sync auto-traits work correctly
// 3. Multiple threads can access different fields safely
// 4. Lock contention doesn't break view type semantics

use std::sync::{Arc, Mutex};
use std::thread;

// =============================================================================
// Test 1: Basic Arc<Mutex<T>> with View-Typed Methods
// =============================================================================

struct Counter {
    count: usize,
    max: usize,
    name: String,
}

impl Counter {
    fn increment(&{mut count} mut self) {
        self.count += 1;
    }

    fn get_count(&{count} self) -> usize {
        self.count
    }

    fn get_max(&{max} self) -> usize {
        self.max
    }

    fn set_name(&{mut name} mut self, new_name: String) {
        self.name = new_name;
    }

    fn update_count_and_max(&{mut count, mut max} mut self) {
        self.count += 1;
        if self.count > self.max {
            self.max = self.count;
        }
    }
}

fn test_basic_arc_mutex() {
    let counter = Arc::new(Mutex::new(Counter {
        count: 0,
        max: 0,
        name: String::from("counter"),
    }));

    // Lock and call view-typed method
    {
        let mut guard = counter.lock().unwrap();
        guard.increment();
        let val = guard.get_count();
        assert_eq!(val, 1);
    }

    // Lock again and modify different field
    {
        let mut guard = counter.lock().unwrap();
        guard.set_name(String::from("updated"));
    }

    println!("Basic Arc<Mutex<T>> with view types: OK");
}

// =============================================================================
// Test 2: Cross-Thread Usage - Single Field Access
// =============================================================================

fn test_cross_thread_single_field() {
    let counter = Arc::new(Mutex::new(Counter {
        count: 0,
        max: 100,
        name: String::from("shared"),
    }));

    let mut handles = vec![];

    // Spawn 10 threads, each increments count 10 times
    for i in 0..10 {
        let counter_clone = Arc::clone(&counter);
        let handle = thread::spawn(move || {
            for _ in 0..10 {
                let mut guard = counter_clone.lock().unwrap();
                guard.increment(); // View-typed method through Arc<Mutex<T>>
            }
        });
        handles.push(handle);
    }

    // Wait for all threads
    for handle in handles {
        handle.join().unwrap();
    }

    // Verify final count
    let guard = counter.lock().unwrap();
    let final_count = guard.get_count();
    assert_eq!(final_count, 100);

    println!("Cross-thread single field access: OK");
}

// =============================================================================
// Test 3: Cross-Thread Usage - Multi-Field Access
// =============================================================================

fn test_cross_thread_multi_field() {
    let counter = Arc::new(Mutex::new(Counter {
        count: 0,
        max: 0,
        name: String::from("multi"),
    }));

    let mut handles = vec![];

    // Spawn threads that update both count and max
    for _ in 0..5 {
        let counter_clone = Arc::clone(&counter);
        let handle = thread::spawn(move || {
            for _ in 0..20 {
                let mut guard = counter_clone.lock().unwrap();
                guard.update_count_and_max(); // Multi-field view-typed method
            }
        });
        handles.push(handle);
    }

    // Wait for all threads
    for handle in handles {
        handle.join().unwrap();
    }

    // Verify results
    let guard = counter.lock().unwrap();
    assert_eq!(guard.get_count(), 100);
    assert_eq!(guard.get_max(), 100);

    println!("Cross-thread multi-field access: OK");
}

// =============================================================================
// Test 4: Send/Sync Verification
// =============================================================================

// Helper function to verify Send
fn assert_send<T: Send>() {}

// Helper function to verify Sync
fn assert_sync<T: Sync>() {}

fn test_send_sync() {
    // Counter itself doesn't need to be Send/Sync
    // Arc<Mutex<Counter>> provides Send/Sync

    assert_send::<Arc<Mutex<Counter>>>();
    assert_sync::<Arc<Mutex<Counter>>>();

    // Verify we can pass Arc<Mutex<Counter>> across thread boundary
    let counter = Arc::new(Mutex::new(Counter {
        count: 0,
        max: 0,
        name: String::from("test"),
    }));

    let counter_clone = Arc::clone(&counter);
    let handle = thread::spawn(move || {
        let mut guard = counter_clone.lock().unwrap();
        guard.increment();
    });

    handle.join().unwrap();

    println!("Send/Sync verification: OK");
}

// =============================================================================
// Test 5: Real-World Pattern - Database Cache
// =============================================================================

struct DatabaseCache {
    cache: std::collections::HashMap<String, String>,
    hits: usize,
    misses: usize,
}

impl DatabaseCache {
    fn new() -> Self {
        DatabaseCache {
            cache: std::collections::HashMap::new(),
            hits: 0,
            misses: 0,
        }
    }

    fn insert(&{mut cache} mut self, key: String, value: String) {
        self.cache.insert(key, value);
    }

    fn record_hit(&{mut hits} mut self) {
        self.hits += 1;
    }

    fn record_miss(&{mut misses} mut self) {
        self.misses += 1;
    }

    fn get_stats(&{hits, misses} self) -> (usize, usize) {
        (self.hits, self.misses)
    }
}

fn test_database_cache_pattern() {
    let cache = Arc::new(Mutex::new(DatabaseCache::new()));

    // Thread 1: Insert data
    let cache1 = Arc::clone(&cache);
    let h1 = thread::spawn(move || {
        for i in 0..50 {
            let mut guard = cache1.lock().unwrap();
            guard.insert(format!("key{}", i), format!("value{}", i));
        }
    });

    // Thread 2: Record hits
    let cache2 = Arc::clone(&cache);
    let h2 = thread::spawn(move || {
        for _ in 0..30 {
            let mut guard = cache2.lock().unwrap();
            guard.record_hit();
        }
    });

    // Thread 3: Record misses
    let cache3 = Arc::clone(&cache);
    let h3 = thread::spawn(move || {
        for _ in 0..20 {
            let mut guard = cache3.lock().unwrap();
            guard.record_miss();
        }
    });

    h1.join().unwrap();
    h2.join().unwrap();
    h3.join().unwrap();

    // Verify stats
    let guard = cache.lock().unwrap();
    let (hits, misses) = guard.get_stats();
    assert_eq!(hits, 30);
    assert_eq!(misses, 20);

    println!("Database cache pattern: OK");
}

// =============================================================================
// Test 6: Lock Guard Lifetime with View Types
// =============================================================================

fn test_lock_guard_lifetimes() {
    let counter = Arc::new(Mutex::new(Counter {
        count: 0,
        max: 0,
        name: String::from("test"),
    }));

    // Test that lock guard works correctly with view-typed methods
    {
        let mut guard = counter.lock().unwrap();
        guard.increment();
        let count1 = guard.get_count();

        // Can call multiple view-typed methods on same guard
        guard.increment();
        let count2 = guard.get_count();

        assert_eq!(count2, count1 + 1);
    } // Lock released here

    // Lock again
    {
        let guard = counter.lock().unwrap();
        assert_eq!(guard.get_count(), 2);
    }

    println!("Lock guard lifetimes: OK");
}

// =============================================================================
// Test 7: Nested Locks (Different Mutexes)
// =============================================================================

struct Config {
    setting_a: bool,
    setting_b: bool,
}

impl Config {
    fn toggle_a(&{mut setting_a} mut self) {
        self.setting_a = !self.setting_a;
    }

    fn toggle_b(&{mut setting_b} mut self) {
        self.setting_b = !self.setting_b;
    }
}

fn test_nested_locks() {
    let config1 = Arc::new(Mutex::new(Config {
        setting_a: false,
        setting_b: false,
    }));

    let config2 = Arc::new(Mutex::new(Config {
        setting_a: true,
        setting_b: true,
    }));

    // Lock both mutexes (different structs, so no deadlock)
    {
        let mut guard1 = config1.lock().unwrap();
        let mut guard2 = config2.lock().unwrap();

        guard1.toggle_a(); // View-typed method on first mutex
        guard2.toggle_b(); // View-typed method on second mutex

        // Both locks held simultaneously, no conflict
    }

    println!("Nested locks (different mutexes): OK");
}

// =============================================================================
// Test 8: Arc<Mutex<T>> with Generic Struct
// =============================================================================

struct GenericContainer<T> {
    data: T,
    metadata: String,
    count: usize,
}

impl<T> GenericContainer<T> {
    fn increment_count(&{mut count} mut self) {
        self.count += 1;
    }

    fn update_metadata(&{mut metadata} mut self, new_meta: String) {
        self.metadata = new_meta;
    }

    fn get_count(&{count} self) -> usize {
        self.count
    }
}

fn test_generic_with_arc_mutex() {
    let container = Arc::new(Mutex::new(GenericContainer {
        data: vec![1, 2, 3],
        metadata: String::from("initial"),
        count: 0,
    }));

    let container_clone = Arc::clone(&container);
    let handle = thread::spawn(move || {
        let mut guard = container_clone.lock().unwrap();
        guard.increment_count();
        guard.update_metadata(String::from("updated"));
    });

    handle.join().unwrap();

    let guard = container.lock().unwrap();
    assert_eq!(guard.get_count(), 1);

    println!("Generic struct with Arc<Mutex<T>>: OK");
}

// =============================================================================
// Test 9: Producer-Consumer Pattern
// =============================================================================

struct SharedBuffer {
    buffer: Vec<i32>,
    producer_count: usize,
    consumer_count: usize,
}

impl SharedBuffer {
    fn new() -> Self {
        SharedBuffer {
            buffer: Vec::new(),
            producer_count: 0,
            consumer_count: 0,
        }
    }

    fn produce(&{mut buffer, mut producer_count} mut self, item: i32) {
        self.buffer.push(item);
        self.producer_count += 1;
    }

    fn consume(&{mut buffer, mut consumer_count} mut self) -> Option<i32> {
        self.consumer_count += 1;
        self.buffer.pop()
    }

    fn get_stats(&{producer_count, consumer_count} self) -> (usize, usize) {
        (self.producer_count, self.consumer_count)
    }
}

fn test_producer_consumer() {
    let buffer = Arc::new(Mutex::new(SharedBuffer::new()));

    // Producer thread
    let producer_buffer = Arc::clone(&buffer);
    let producer = thread::spawn(move || {
        for i in 0..100 {
            let mut guard = producer_buffer.lock().unwrap();
            guard.produce(i);
        }
    });

    // Consumer thread
    let consumer_buffer = Arc::clone(&buffer);
    let consumer = thread::spawn(move || {
        for _ in 0..50 {
            let mut guard = consumer_buffer.lock().unwrap();
            guard.consume();
        }
    });

    producer.join().unwrap();
    consumer.join().unwrap();

    let guard = buffer.lock().unwrap();
    let (produced, consumed) = guard.get_stats();
    assert_eq!(produced, 100);
    assert_eq!(consumed, 50);

    println!("Producer-consumer pattern: OK");
}

// =============================================================================
// Main Test Runner
// =============================================================================

fn main() {
    test_basic_arc_mutex();
    test_cross_thread_single_field();
    test_cross_thread_multi_field();
    test_send_sync();
    test_database_cache_pattern();
    test_lock_guard_lifetimes();
    test_nested_locks();
    test_generic_with_arc_mutex();
    test_producer_consumer();

    println!("\n✓ All Arc<Mutex<T>> concurrency tests passed!");
    println!("✓ View-typed methods work correctly through Arc<Mutex<T>>");
    println!("✓ Send/Sync auto-traits work as expected");
    println!("✓ Cross-thread access to different fields is safe");
    println!("✓ Lock guards interact properly with view type semantics");
    println!("✓ Real-world concurrency patterns (cache, producer-consumer) work");
}
