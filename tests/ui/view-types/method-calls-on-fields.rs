//@ check-pass
#![feature(view_types)]
#![allow(unused, incomplete_features)]

// METHOD CALLS ON FIELDS TEST
//
// This test verifies that you can call methods on fields accessed through
// view types. This is critical for real-world usage - if you can access a
// field, you should be able to use its full API.
//
// Key scenarios:
// 1. Vec methods (push, pop, len, iter, etc.)
// 2. String methods (push_str, len, as_str, etc.)
// 3. Option/Result methods (unwrap, map, etc.)
// 4. Custom type methods
// 5. Chained method calls
// 6. Methods returning references with correct lifetimes

// =============================================================================
// Test 1: Vec Methods Through View Types
// =============================================================================

struct WithVec {
    items: Vec<i32>,
    metadata: String,
}

impl WithVec {
    fn add_item(&{mut items} mut self, value: i32) {
        self.items.push(value);  // Method call on viewed field
    }

    fn item_count(&{items} self) -> usize {
        self.items.len()  // Immutable method call
    }

    fn first_item(&{items} self) -> Option<&i32> {
        self.items.first()  // Returns reference with correct lifetime
    }

    fn clear_items(&{mut items} mut self) {
        self.items.clear();
    }

    fn sort_items(&{mut items} mut self) {
        self.items.sort();
    }

    fn iterate_items(&{items} self) -> i32 {
        self.items.iter().sum()  // Iterator method
    }

    fn filter_items(&{items} self) -> Vec<i32> {
        self.items.iter()
            .filter(|&&x| x > 10)
            .copied()
            .collect()  // Chained iterator methods
    }

    fn reserve_space(&{mut items} mut self, additional: usize) {
        self.items.reserve(additional);
    }

    fn pop_item(&{mut items} mut self) -> Option<i32> {
        self.items.pop()
    }

    fn extend_items(&{mut items} mut self, other: Vec<i32>) {
        self.items.extend(other);
    }
}

// =============================================================================
// Test 2: String Methods Through View Types
// =============================================================================

struct WithString {
    name: String,
    description: String,
    count: usize,
}

impl WithString {
    fn append_name(&{mut name} mut self, suffix: &str) {
        self.name.push_str(suffix);
    }

    fn name_length(&{name} self) -> usize {
        self.name.len()
    }

    fn name_as_str(&{name} self) -> String {
        self.name.clone()
    }

    fn clear_name(&{mut name} mut self) {
        self.name.clear();
    }

    fn name_contains(&{name} self, pattern: &str) -> bool {
        self.name.contains(pattern)
    }

    fn name_to_uppercase(&{name} self) -> String {
        self.name.to_uppercase()
    }

    fn truncate_name(&{mut name} mut self, new_len: usize) {
        self.name.truncate(new_len);
    }

    fn name_bytes(&{name} self) -> Vec<u8> {
        self.name.bytes().collect()
    }

    fn name_chars(&{name} self) -> Vec<char> {
        self.name.chars().collect()
    }
}

// =============================================================================
// Test 3: Option Methods Through View Types
// =============================================================================

struct WithOption {
    maybe_value: Option<i32>,
    maybe_string: Option<String>,
    counter: usize,
}

impl WithOption {
    fn is_some(&{maybe_value} self) -> bool {
        self.maybe_value.is_some()
    }

    fn is_none(&{maybe_value} self) -> bool {
        self.maybe_value.is_none()
    }

    fn get_or_default(&{maybe_value} self) -> i32 {
        self.maybe_value.unwrap_or(0)
    }

    fn map_value(&{maybe_value} self) -> Option<i32> {
        self.maybe_value.map(|x| x * 2)
    }

    fn take_value(&{mut maybe_value} mut self) -> Option<i32> {
        self.maybe_value.take()
    }

    fn replace_value(&{mut maybe_value} mut self, new_val: i32) -> Option<i32> {
        self.maybe_value.replace(new_val)
    }

    fn as_ref_value(&{maybe_value} self) -> Option<&i32> {
        self.maybe_value.as_ref()
    }

    fn as_mut_value(&{mut maybe_value} mut self) -> Option<&mut i32> {
        self.maybe_value.as_mut()
    }

    fn filter_value(&{maybe_value} self) -> Option<i32> {
        self.maybe_value.filter(|&x| x > 10)
    }
}

// =============================================================================
// Test 4: Result Methods Through View Types
// =============================================================================

struct WithResult {
    result: Result<i32, String>,
    backup: i32,
}

impl WithResult {
    fn is_ok(&{result} self) -> bool {
        self.result.is_ok()
    }

    fn is_err(&{result} self) -> bool {
        self.result.is_err()
    }

    fn unwrap_or_backup(&{result, backup} self) -> i32 {
        self.result.as_ref().copied().unwrap_or(self.backup)
    }

    fn map_result(&{result} self) -> Result<i32, String> {
        self.result.as_ref().map(|&x| x * 2).map_err(|e| e.clone())
    }

    fn ok_value(&{result} self) -> Option<i32> {
        self.result.as_ref().ok().copied()
    }

    fn err_value(&{result} self) -> Option<String> {
        self.result.as_ref().err().cloned()
    }
}

// =============================================================================
// Test 5: Custom Type Methods Through View Types
// =============================================================================

struct Point {
    x: f32,
    y: f32,
}

impl Point {
    fn distance_from_origin(&self) -> f32 {
        (self.x * self.x + self.y * self.y).sqrt()
    }

    fn translate(&mut self, dx: f32, dy: f32) {
        self.x += dx;
        self.y += dy;
    }

    fn scale(&mut self, factor: f32) {
        self.x *= factor;
        self.y *= factor;
    }
}

struct WithCustomType {
    position: Point,
    velocity: Point,
    name: String,
}

impl WithCustomType {
    fn position_distance(&{position} self) -> f32 {
        self.position.distance_from_origin()  // Method on custom type
    }

    fn move_position(&{mut position} mut self, dx: f32, dy: f32) {
        self.position.translate(dx, dy);  // Mutable method on custom type
    }

    fn scale_velocity(&{mut velocity} mut self, factor: f32) {
        self.velocity.scale(factor);
    }

    fn total_speed(&{velocity} self) -> f32 {
        self.velocity.distance_from_origin()
    }
}

// =============================================================================
// Test 6: Chained Method Calls
// =============================================================================

struct WithChaining {
    text: String,
    numbers: Vec<i32>,
}

impl WithChaining {
    fn process_text(&{text} self) -> String {
        self.text
            .trim()
            .to_lowercase()
            .replace(" ", "_")  // Multiple chained calls
    }

    fn sum_positive_evens(&{numbers} self) -> i32 {
        self.numbers
            .iter()
            .filter(|&&x| x > 0)
            .filter(|&&x| x % 2 == 0)
            .sum()  // Long chain
    }

    fn transform_numbers(&{numbers} self) -> Vec<String> {
        self.numbers
            .iter()
            .map(|x| x * 2)
            .filter(|&x| x > 10)
            .map(|x| format!("num_{}", x))
            .collect()  // Complex transformation chain
    }
}

// =============================================================================
// Test 7: Methods Returning References
// =============================================================================

struct Container {
    data: Vec<String>,
    cache: Vec<i32>,
}

impl Container {
    fn first_string(&{data} self) -> Option<&String> {
        self.data.first()  // Returns reference to element
    }

    fn last_string(&{data} self) -> Option<&String> {
        self.data.last()
    }

    fn get_string(&{data} self, index: usize) -> Option<&String> {
        self.data.get(index)
    }

    fn all_strings(&{data} self) -> Vec<String> {
        self.data.clone()
    }

    fn first_cache(&{cache} self) -> Option<&i32> {
        self.cache.first()
    }
}

// =============================================================================
// Test 8: Methods with Multiple Parameters
// =============================================================================

struct WithMethods {
    buffer: Vec<u8>,
    config: String,
}

impl WithMethods {
    fn insert_at(&{mut buffer} mut self, index: usize, value: u8) {
        self.buffer.insert(index, value);
    }

    fn extend_from_slice(&{mut buffer} mut self, slice: &[u8]) {
        self.buffer.extend_from_slice(slice);
    }

    // split_at removed - would return references (V1 restriction)
    // Use case is covered by other buffer access methods

    fn starts_with(&{buffer} self, prefix: &[u8]) -> bool {
        self.buffer.starts_with(prefix)
    }
}

// =============================================================================
// Test 9: Methods with Closures
// =============================================================================

struct WithClosures {
    values: Vec<i32>,
    threshold: i32,
}

impl WithClosures {
    fn find_first_above(&{values, threshold} self) -> Option<i32> {
        self.values
            .iter()
            .find(|&&x| x > self.threshold)
            .copied()
    }

    fn count_above(&{values, threshold} self) -> usize {
        self.values.iter().filter(|&&x| x > self.threshold).count()
    }

    fn any_above(&{values, threshold} self) -> bool {
        self.values.iter().any(|&x| x > self.threshold)
    }

    fn all_above(&{values, threshold} self) -> bool {
        self.values.iter().all(|&x| x > self.threshold)
    }

    fn partition_by_threshold(&{values, threshold} self) -> (Vec<i32>, Vec<i32>) {
        self.values
            .iter()
            .partition(|&&x| x > self.threshold)
    }
}

// =============================================================================
// Test 10: Real-World Pattern - Entity Component System
// =============================================================================

struct Health {
    current: f32,
    max: f32,
}

impl Health {
    fn is_alive(&self) -> bool {
        self.current > 0.0
    }

    fn percentage(&self) -> f32 {
        (self.current / self.max) * 100.0
    }

    fn damage(&mut self, amount: f32) {
        self.current = (self.current - amount).max(0.0);
    }

    fn heal(&mut self, amount: f32) {
        self.current = (self.current + amount).min(self.max);
    }
}

struct Entity {
    health: Health,
    position: Point,
    inventory: Vec<String>,
}

impl Entity {
    fn is_alive(&{health} self) -> bool {
        self.health.is_alive()  // Call method on field
    }

    fn health_percentage(&{health} self) -> f32 {
        self.health.percentage()
    }

    fn take_damage(&{mut health} mut self, amount: f32) {
        self.health.damage(amount);
    }

    fn heal_up(&{mut health} mut self, amount: f32) {
        self.health.heal(amount);
    }

    fn move_to(&{mut position} mut self, x: f32, y: f32) {
        self.position.x = x;
        self.position.y = y;
    }

    fn distance_from_origin(&{position} self) -> f32 {
        self.position.distance_from_origin()
    }

    fn add_item(&{mut inventory} mut self, item: String) {
        self.inventory.push(item);
    }

    fn has_item(&{inventory} self, item: &str) -> bool {
        self.inventory.iter().any(|i| i == item)
    }

    fn item_count(&{inventory} self) -> usize {
        self.inventory.len()
    }
}

// =============================================================================
// Main: Test all method call patterns
// =============================================================================

fn main() {
    // Test Vec methods
    let mut wv = WithVec {
        items: vec![1, 2, 3],
        metadata: String::from("test"),
    };
    wv.add_item(4);
    assert_eq!(wv.item_count(), 4);
    assert_eq!(wv.first_item(), Some(&1));
    assert_eq!(wv.iterate_items(), 10);
    wv.sort_items();
    wv.reserve_space(10);
    let filtered = wv.filter_items();
    assert_eq!(filtered, vec![]);

    // Test String methods
    let mut ws = WithString {
        name: String::from("hello"),
        description: String::from("world"),
        count: 0,
    };
    ws.append_name(" world");
    assert_eq!(ws.name_length(), 11);
    assert_eq!(ws.name_as_str(), "hello world");
    assert!(ws.name_contains("world"));
    let upper = ws.name_to_uppercase();
    assert_eq!(upper, "HELLO WORLD");

    // Test Option methods
    let mut wo = WithOption {
        maybe_value: Some(42),
        maybe_string: None,
        counter: 0,
    };
    assert!(wo.is_some());
    assert!(!wo.is_none());
    assert_eq!(wo.get_or_default(), 42);
    assert_eq!(wo.map_value(), Some(84));
    let taken = wo.take_value();
    assert_eq!(taken, Some(42));
    assert!(wo.is_none());

    // Test Result methods
    let wr = WithResult {
        result: Ok(100),
        backup: 0,
    };
    assert!(wr.is_ok());
    assert!(!wr.is_err());
    assert_eq!(wr.unwrap_or_backup(), 100);

    // Test custom type methods
    let mut wc = WithCustomType {
        position: Point { x: 3.0, y: 4.0 },
        velocity: Point { x: 1.0, y: 1.0 },
        name: String::from("player"),
    };
    let dist = wc.position_distance();
    assert_eq!(dist, 5.0);
    wc.move_position(1.0, 1.0);
    assert_eq!(wc.position.x, 4.0);
    assert_eq!(wc.position.y, 5.0);

    // Test chained methods
    let wch = WithChaining {
        text: String::from("  Hello World  "),
        numbers: vec![1, 2, 3, 4, 5, 6],
    };
    let processed = wch.process_text();
    assert_eq!(processed, "__hello_world__");
    let sum = wch.sum_positive_evens();
    assert_eq!(sum, 12);

    // Test reference returns
    let cont = Container {
        data: vec![String::from("first"), String::from("second")],
        cache: vec![1, 2, 3],
    };
    assert_eq!(cont.first_string(), Some(&String::from("first")));
    assert_eq!(cont.last_string(), Some(&String::from("second")));
    let all = cont.all_strings();
    assert_eq!(all.len(), 2);

    // Test closures
    let wcl = WithClosures {
        values: vec![5, 10, 15, 20],
        threshold: 12,
    };
    assert_eq!(wcl.find_first_above(), Some(15));
    assert_eq!(wcl.count_above(), 2);
    assert!(wcl.any_above());
    assert!(!wcl.all_above());

    // Test entity system
    let mut entity = Entity {
        health: Health { current: 100.0, max: 100.0 },
        position: Point { x: 0.0, y: 0.0 },
        inventory: vec![],
    };
    assert!(entity.is_alive());
    assert_eq!(entity.health_percentage(), 100.0);
    entity.take_damage(30.0);
    assert_eq!(entity.health.current, 70.0);
    entity.heal_up(15.0);
    assert_eq!(entity.health.current, 85.0);
    entity.add_item(String::from("sword"));
    assert!(entity.has_item("sword"));
    assert_eq!(entity.item_count(), 1);

    println!("✓ All method call tests passed!");
}
