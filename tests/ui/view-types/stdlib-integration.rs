//@ check-pass
#![feature(view_types)]
#![allow(unused, incomplete_features)]

// STANDARD LIBRARY INTEGRATION TEST
//
// This test verifies that view types work correctly with Rust standard library
// types. This is critical for real-world usage since most code uses stdlib.
//
// Tested stdlib types:
// - Collections: Vec, HashMap, HashSet, BTreeMap, BTreeSet, VecDeque, LinkedList
// - Smart pointers: Box, Rc, Arc (as field types, not wrapping view types)
// - Interior mutability: Cell, RefCell
// - Other: String, Option, Result, Range types
//
// Note: View types on trait objects like Box<dyn Trait> are not supported in V1

use std::collections::{HashMap, HashSet, BTreeMap, BTreeSet, VecDeque, LinkedList};
use std::cell::{Cell, RefCell};
use std::rc::Rc;
use std::sync::Arc;

// =============================================================================
// Test 1: Vec<T> as Field
// =============================================================================

struct WithVec {
    numbers: Vec<i32>,
    strings: Vec<String>,
    metadata: String,
}

impl WithVec {
    fn add_number(&{mut numbers} mut self, n: i32) {
        self.numbers.push(n);
    }

    fn number_count(&{numbers} self) -> usize {
        self.numbers.len()
    }

    fn add_string(&{mut strings} mut self, s: String) {
        self.strings.push(s);
    }

    fn string_count(&{strings} self) -> usize {
        self.strings.len()
    }

    fn total_count(&{numbers, strings} self) -> usize {
        self.numbers.len() + self.strings.len()
    }
}

// =============================================================================
// Test 2: HashMap<K, V> as Field
// =============================================================================

struct WithHashMap {
    scores: HashMap<String, i32>,
    cache: HashMap<i32, String>,
    config: String,
}

impl WithHashMap {
    fn set_score(&{mut scores} mut self, name: String, score: i32) {
        self.scores.insert(name, score);
    }

    fn get_score(&{scores} self, name: &str) -> Option<i32> {
        self.scores.get(name).copied()
    }

    fn score_count(&{scores} self) -> usize {
        self.scores.len()
    }

    fn cache_value(&{mut cache} mut self, key: i32, value: String) {
        self.cache.insert(key, value);
    }

    fn get_cached(&{cache} self, key: i32) -> Option<&String> {
        self.cache.get(&key)
    }

    fn clear_cache(&{mut cache} mut self) {
        self.cache.clear();
    }

    fn has_score(&{scores} self, name: &str) -> bool {
        self.scores.contains_key(name)
    }
}

// =============================================================================
// Test 3: HashSet<T> as Field
// =============================================================================

struct WithHashSet {
    tags: HashSet<String>,
    visited: HashSet<i32>,
    name: String,
}

impl WithHashSet {
    fn add_tag(&{mut tags} mut self, tag: String) {
        self.tags.insert(tag);
    }

    fn has_tag(&{tags} self, tag: &str) -> bool {
        self.tags.contains(tag)
    }

    fn tag_count(&{tags} self) -> usize {
        self.tags.len()
    }

    fn mark_visited(&{mut visited} mut self, id: i32) {
        self.visited.insert(id);
    }

    fn was_visited(&{visited} self, id: i32) -> bool {
        self.visited.contains(&id)
    }

    fn clear_visited(&{mut visited} mut self) {
        self.visited.clear();
    }
}

// =============================================================================
// Test 4: BTreeMap<K, V> as Field
// =============================================================================

struct WithBTreeMap {
    sorted_data: BTreeMap<i32, String>,
    index: BTreeMap<String, Vec<i32>>,
    counter: usize,
}

impl WithBTreeMap {
    fn insert_data(&{mut sorted_data} mut self, key: i32, value: String) {
        self.sorted_data.insert(key, value);
    }

    fn get_data(&{sorted_data} self, key: i32) -> Option<&String> {
        self.sorted_data.get(&key)
    }

    fn first_key(&{sorted_data} self) -> Option<i32> {
        self.sorted_data.keys().next().copied()
    }

    fn last_key(&{sorted_data} self) -> Option<i32> {
        self.sorted_data.keys().last().copied()
    }

    fn range_count(&{sorted_data} self, start: i32, end: i32) -> usize {
        self.sorted_data.range(start..end).count()
    }
}

// =============================================================================
// Test 5: BTreeSet<T> as Field
// =============================================================================

struct WithBTreeSet {
    ordered_ids: BTreeSet<i32>,
    priority_queue: BTreeSet<String>,
    metadata: String,
}

impl WithBTreeSet {
    fn add_id(&{mut ordered_ids} mut self, id: i32) {
        self.ordered_ids.insert(id);
    }

    fn min_id(&{ordered_ids} self) -> Option<i32> {
        self.ordered_ids.iter().next().copied()
    }

    fn max_id(&{ordered_ids} self) -> Option<i32> {
        self.ordered_ids.iter().last().copied()
    }

    fn id_count(&{ordered_ids} self) -> usize {
        self.ordered_ids.len()
    }

    fn contains_id(&{ordered_ids} self, id: i32) -> bool {
        self.ordered_ids.contains(&id)
    }
}

// =============================================================================
// Test 6: VecDeque<T> as Field
// =============================================================================

struct WithVecDeque {
    queue: VecDeque<i32>,
    buffer: VecDeque<String>,
    size: usize,
}

impl WithVecDeque {
    fn push_back(&{mut queue} mut self, value: i32) {
        self.queue.push_back(value);
    }

    fn push_front(&{mut queue} mut self, value: i32) {
        self.queue.push_front(value);
    }

    fn pop_front(&{mut queue} mut self) -> Option<i32> {
        self.queue.pop_front()
    }

    fn pop_back(&{mut queue} mut self) -> Option<i32> {
        self.queue.pop_back()
    }

    fn queue_len(&{queue} self) -> usize {
        self.queue.len()
    }

    fn front(&{queue} self) -> Option<&i32> {
        self.queue.front()
    }

    fn back(&{queue} self) -> Option<&i32> {
        self.queue.back()
    }
}

// =============================================================================
// Test 7: LinkedList<T> as Field
// =============================================================================

struct WithLinkedList {
    list: LinkedList<i32>,
    backup: LinkedList<String>,
    counter: usize,
}

impl WithLinkedList {
    fn push_back(&{mut list} mut self, value: i32) {
        self.list.push_back(value);
    }

    fn push_front(&{mut list} mut self, value: i32) {
        self.list.push_front(value);
    }

    fn pop_front(&{mut list} mut self) -> Option<i32> {
        self.list.pop_front()
    }

    fn pop_back(&{mut list} mut self) -> Option<i32> {
        self.list.pop_back()
    }

    fn list_len(&{list} self) -> usize {
        self.list.len()
    }

    fn is_empty(&{list} self) -> bool {
        self.list.is_empty()
    }
}

// =============================================================================
// Test 8: Box<T> as Field Type
// =============================================================================

struct WithBox {
    boxed_value: Box<i32>,
    boxed_string: Box<String>,
    counter: usize,
}

impl WithBox {
    fn get_value(&{boxed_value} self) -> i32 {
        *self.boxed_value
    }

    fn set_value(&{mut boxed_value} mut self, value: i32) {
        *self.boxed_value = value;
    }

    fn get_string(&{boxed_string} self) -> String {
        (*self.boxed_string).clone()
    }

    fn append_string(&{mut boxed_string} mut self, suffix: &str) {
        self.boxed_string.push_str(suffix);
    }

    fn string_len(&{boxed_string} self) -> usize {
        self.boxed_string.len()
    }
}

// =============================================================================
// Test 9: Rc<T> as Field Type
// =============================================================================

struct WithRc {
    shared_value: Rc<Vec<i32>>,
    shared_string: Rc<String>,
    local: i32,
}

impl WithRc {
    fn value_len(&{shared_value} self) -> usize {
        self.shared_value.len()
    }

    fn value_sum(&{shared_value} self) -> i32 {
        self.shared_value.iter().sum()
    }

    fn string_len(&{shared_string} self) -> usize {
        self.shared_string.len()
    }

    fn string_clone(&{shared_string} self) -> Rc<String> {
        Rc::clone(&self.shared_string)
    }

    fn strong_count(&{shared_value} self) -> usize {
        Rc::strong_count(&self.shared_value)
    }
}

// =============================================================================
// Test 10: Arc<T> as Field Type (Thread-Safe)
// =============================================================================

struct WithArc {
    shared_data: Arc<Vec<i32>>,
    shared_config: Arc<String>,
    counter: usize,
}

impl WithArc {
    fn data_len(&{shared_data} self) -> usize {
        self.shared_data.len()
    }

    fn data_sum(&{shared_data} self) -> i32 {
        self.shared_data.iter().sum()
    }

    fn config_clone(&{shared_config} self) -> Arc<String> {
        Arc::clone(&self.shared_config)
    }

    fn config_len(&{shared_config} self) -> usize {
        self.shared_config.len()
    }

    fn strong_count(&{shared_data} self) -> usize {
        Arc::strong_count(&self.shared_data)
    }
}

// =============================================================================
// Test 11: Cell<T> as Field Type (Interior Mutability)
// =============================================================================

struct WithCell {
    cell_value: Cell<i32>,
    cell_bool: Cell<bool>,
    name: String,
}

impl WithCell {
    fn get_value(&{cell_value} self) -> i32 {
        self.cell_value.get()
    }

    fn set_value(&{cell_value} self, value: i32) {
        self.cell_value.set(value);
    }

    fn increment(&{cell_value} self) {
        let current = self.cell_value.get();
        self.cell_value.set(current + 1);
    }

    fn get_bool(&{cell_bool} self) -> bool {
        self.cell_bool.get()
    }

    fn toggle_bool(&{cell_bool} self) {
        self.cell_bool.set(!self.cell_bool.get());
    }

    fn both_values(&{cell_value, cell_bool} self) -> (i32, bool) {
        (self.cell_value.get(), self.cell_bool.get())
    }
}

// =============================================================================
// Test 12: RefCell<T> as Field Type (Interior Mutability)
// =============================================================================

struct WithRefCell {
    ref_cell_vec: RefCell<Vec<i32>>,
    ref_cell_string: RefCell<String>,
    counter: usize,
}

impl WithRefCell {
    fn vec_len(&{ref_cell_vec} self) -> usize {
        self.ref_cell_vec.borrow().len()
    }

    fn add_to_vec(&{ref_cell_vec} self, value: i32) {
        self.ref_cell_vec.borrow_mut().push(value);
    }

    fn vec_sum(&{ref_cell_vec} self) -> i32 {
        self.ref_cell_vec.borrow().iter().sum()
    }

    fn string_len(&{ref_cell_string} self) -> usize {
        self.ref_cell_string.borrow().len()
    }

    fn append_string(&{ref_cell_string} self, suffix: &str) {
        self.ref_cell_string.borrow_mut().push_str(suffix);
    }

    fn get_string(&{ref_cell_string} self) -> String {
        self.ref_cell_string.borrow().clone()
    }
}

// =============================================================================
// Test 13: Nested Collections
// =============================================================================

struct WithNestedCollections {
    vec_of_vecs: Vec<Vec<i32>>,
    map_of_vecs: HashMap<String, Vec<i32>>,
    counter: usize,
}

impl WithNestedCollections {
    fn add_inner_vec(&{mut vec_of_vecs} mut self, vec: Vec<i32>) {
        self.vec_of_vecs.push(vec);
    }

    fn total_elements(&{vec_of_vecs} self) -> usize {
        self.vec_of_vecs.iter().map(|v| v.len()).sum()
    }

    fn insert_map_entry(&{mut map_of_vecs} mut self, key: String, value: Vec<i32>) {
        self.map_of_vecs.insert(key, value);
    }

    fn get_map_entry(&{map_of_vecs} self, key: &str) -> Option<&Vec<i32>> {
        self.map_of_vecs.get(key)
    }

    fn map_total_elements(&{map_of_vecs} self) -> usize {
        self.map_of_vecs.values().map(|v| v.len()).sum()
    }
}

// =============================================================================
// Test 14: Option and Result with Complex Types
// =============================================================================

struct WithComplexOptions {
    maybe_vec: Option<Vec<i32>>,
    maybe_map: Option<HashMap<String, i32>>,
    result: Result<Vec<String>, String>,
    counter: usize,
}

impl WithComplexOptions {
    fn vec_len(&{maybe_vec} self) -> Option<usize> {
        self.maybe_vec.as_ref().map(|v| v.len())
    }

    fn take_vec(&{mut maybe_vec} mut self) -> Option<Vec<i32>> {
        self.maybe_vec.take()
    }

    fn map_len(&{maybe_map} self) -> Option<usize> {
        self.maybe_map.as_ref().map(|m| m.len())
    }

    fn result_len(&{result} self) -> Result<usize, String> {
        self.result.as_ref().map(|v| v.len()).map_err(|e| e.clone())
    }
}

// =============================================================================
// Test 15: Real-World Pattern - Cache with Multiple Backing Stores
// =============================================================================

struct Cache {
    memory: HashMap<String, String>,
    indexes: HashMap<String, Vec<String>>,
    metadata: BTreeMap<String, i64>,
    stats: RefCell<CacheStats>,
}

struct CacheStats {
    hits: usize,
    misses: usize,
}

impl Cache {
    fn get(&{memory, stats} self, key: &str) -> Option<&String> {
        let result = self.memory.get(key);
        if result.is_some() {
            self.stats.borrow_mut().hits += 1;
        } else {
            self.stats.borrow_mut().misses += 1;
        }
        result
    }

    fn insert(&{mut memory} mut self, key: String, value: String) {
        self.memory.insert(key, value);
    }

    fn add_to_index(&{mut indexes} mut self, index_key: String, value: String) {
        self.indexes.entry(index_key).or_insert_with(Vec::new).push(value);
    }

    fn get_index(&{indexes} self, index_key: &str) -> Option<&Vec<String>> {
        self.indexes.get(index_key)
    }

    fn set_metadata(&{mut metadata} mut self, key: String, timestamp: i64) {
        self.metadata.insert(key, timestamp);
    }

    fn get_metadata(&{metadata} self, key: &str) -> Option<i64> {
        self.metadata.get(key).copied()
    }

    fn hit_rate(&{stats} self) -> f64 {
        let stats = self.stats.borrow();
        let total = stats.hits + stats.misses;
        if total == 0 {
            0.0
        } else {
            stats.hits as f64 / total as f64
        }
    }
}

// =============================================================================
// Main: Test all standard library integrations
// =============================================================================

fn main() {
    // Test Vec
    let mut wv = WithVec {
        numbers: vec![1, 2, 3],
        strings: vec![String::from("a")],
        metadata: String::from("test"),
    };
    wv.add_number(4);
    assert_eq!(wv.number_count(), 4);
    wv.add_string(String::from("b"));
    assert_eq!(wv.string_count(), 2);
    assert_eq!(wv.total_count(), 6);

    // Test HashMap
    let mut whm = WithHashMap {
        scores: HashMap::new(),
        cache: HashMap::new(),
        config: String::from("config"),
    };
    whm.set_score(String::from("alice"), 100);
    assert_eq!(whm.get_score("alice"), Some(100));
    assert!(whm.has_score("alice"));
    whm.cache_value(1, String::from("cached"));
    assert_eq!(whm.get_cached(1), Some(&String::from("cached")));

    // Test HashSet
    let mut whs = WithHashSet {
        tags: HashSet::new(),
        visited: HashSet::new(),
        name: String::from("test"),
    };
    whs.add_tag(String::from("rust"));
    assert!(whs.has_tag("rust"));
    assert_eq!(whs.tag_count(), 1);
    whs.mark_visited(42);
    assert!(whs.was_visited(42));

    // Test BTreeMap
    let mut wbm = WithBTreeMap {
        sorted_data: BTreeMap::new(),
        index: BTreeMap::new(),
        counter: 0,
    };
    wbm.insert_data(1, String::from("one"));
    wbm.insert_data(2, String::from("two"));
    assert_eq!(wbm.get_data(1), Some(&String::from("one")));
    assert_eq!(wbm.first_key(), Some(1));
    assert_eq!(wbm.last_key(), Some(2));

    // Test BTreeSet
    let mut wbs = WithBTreeSet {
        ordered_ids: BTreeSet::new(),
        priority_queue: BTreeSet::new(),
        metadata: String::from("test"),
    };
    wbs.add_id(5);
    wbs.add_id(1);
    wbs.add_id(3);
    assert_eq!(wbs.min_id(), Some(1));
    assert_eq!(wbs.max_id(), Some(5));
    assert!(wbs.contains_id(3));

    // Test VecDeque
    let mut wvd = WithVecDeque {
        queue: VecDeque::new(),
        buffer: VecDeque::new(),
        size: 0,
    };
    wvd.push_back(1);
    wvd.push_front(0);
    assert_eq!(wvd.front(), Some(&0));
    assert_eq!(wvd.back(), Some(&1));
    assert_eq!(wvd.queue_len(), 2);
    assert_eq!(wvd.pop_front(), Some(0));

    // Test LinkedList
    let mut wll = WithLinkedList {
        list: LinkedList::new(),
        backup: LinkedList::new(),
        counter: 0,
    };
    wll.push_back(1);
    wll.push_front(0);
    assert_eq!(wll.list_len(), 2);
    assert!(!wll.is_empty());
    assert_eq!(wll.pop_front(), Some(0));

    // Test Box
    let mut wb = WithBox {
        boxed_value: Box::new(42),
        boxed_string: Box::new(String::from("hello")),
        counter: 0,
    };
    assert_eq!(wb.get_value(), 42);
    wb.set_value(100);
    assert_eq!(wb.get_value(), 100);
    assert_eq!(wb.get_string(), "hello");
    wb.append_string(" world");
    assert_eq!(wb.string_len(), 11);

    // Test Rc
    let wrc = WithRc {
        shared_value: Rc::new(vec![1, 2, 3]),
        shared_string: Rc::new(String::from("shared")),
        local: 0,
    };
    assert_eq!(wrc.value_len(), 3);
    assert_eq!(wrc.value_sum(), 6);
    assert_eq!(wrc.string_len(), 6);
    let cloned = wrc.string_clone();
    assert_eq!(wrc.strong_count(), 1);

    // Test Arc
    let warc = WithArc {
        shared_data: Arc::new(vec![1, 2, 3, 4]),
        shared_config: Arc::new(String::from("config")),
        counter: 0,
    };
    assert_eq!(warc.data_len(), 4);
    assert_eq!(warc.data_sum(), 10);
    assert_eq!(warc.config_len(), 6);

    // Test Cell
    let wc = WithCell {
        cell_value: Cell::new(42),
        cell_bool: Cell::new(false),
        name: String::from("test"),
    };
    assert_eq!(wc.get_value(), 42);
    wc.set_value(100);
    assert_eq!(wc.get_value(), 100);
    wc.increment();
    assert_eq!(wc.get_value(), 101);
    assert_eq!(wc.get_bool(), false);
    wc.toggle_bool();
    assert_eq!(wc.get_bool(), true);

    // Test RefCell
    let wrc2 = WithRefCell {
        ref_cell_vec: RefCell::new(vec![1, 2, 3]),
        ref_cell_string: RefCell::new(String::from("hello")),
        counter: 0,
    };
    assert_eq!(wrc2.vec_len(), 3);
    wrc2.add_to_vec(4);
    assert_eq!(wrc2.vec_len(), 4);
    assert_eq!(wrc2.vec_sum(), 10);
    wrc2.append_string(" world");
    assert_eq!(wrc2.string_len(), 11);

    // Test nested collections
    let mut wnc = WithNestedCollections {
        vec_of_vecs: vec![],
        map_of_vecs: HashMap::new(),
        counter: 0,
    };
    wnc.add_inner_vec(vec![1, 2, 3]);
    wnc.add_inner_vec(vec![4, 5]);
    assert_eq!(wnc.total_elements(), 5);
    wnc.insert_map_entry(String::from("key1"), vec![1, 2]);
    assert_eq!(wnc.map_total_elements(), 2);

    // Test Cache
    let cache = Cache {
        memory: HashMap::new(),
        indexes: HashMap::new(),
        metadata: BTreeMap::new(),
        stats: RefCell::new(CacheStats { hits: 0, misses: 0 }),
    };
    assert_eq!(cache.get("missing"), None);
    assert_eq!(cache.hit_rate(), 0.0);

    println!("✓ All standard library integration tests passed!");
}
