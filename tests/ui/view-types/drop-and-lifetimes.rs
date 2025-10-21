// V1 RESTRICTION TEST: Return references not allowed
#![feature(view_types)]
#![allow(unused, incomplete_features)]

// DROP AND LIFETIMES TEST - V1 VERSION
//
// This test verifies the V1 restriction: view-typed methods cannot return references.
// This restriction prevents soundness bugs while maintaining core functionality.
//
// Tests that DO work in V1:
// 1. Drop implementations on fields
// 2. View-typed methods returning VALUES (usize, i32, etc.)
// 3. Disjoint field borrowing with Drop
//
// Tests that are RESTRICTED in V1:
// 1. View-typed methods returning references (tested with error annotations)

use std::cell::RefCell;
use std::rc::Rc;

// =============================================================================
// Test 1: Basic Drop on Fields
// =============================================================================

#[derive(Debug)]
struct DropTracker {
    id: usize,
    log: Rc<RefCell<Vec<String>>>,
}

impl Drop for DropTracker {
    fn drop(&mut self) {
        self.log.borrow_mut().push(format!("dropped_{}", self.id));
    }
}

struct WithDrop {
    tracker_a: DropTracker,
    tracker_b: DropTracker,
    value: i32,
}

impl WithDrop {
    fn use_tracker_a(&{tracker_a} self) -> usize {
        self.tracker_a.id
    }

    fn use_tracker_b(&{tracker_b} self) -> usize {
        self.tracker_b.id
    }

    fn use_value(&{value} self) -> i32 {
        self.value
    }

    fn modify_value(&{mut value} mut self, new_val: i32) {
        self.value = new_val;
    }
}

// =============================================================================
// Test 2: Drop with Mutable Borrows
// =============================================================================

struct Resource {
    data: Vec<i32>,
}

impl Drop for Resource {
    fn drop(&mut self) {
        // Cleanup happens here
    }
}

struct WithResource {
    resource: Resource,
    counter: usize,
    name: String,
}

impl WithResource {
    fn increment_counter(&{mut counter} mut self) {
        self.counter += 1;
    }

    fn get_counter(&{counter} self) -> usize {
        self.counter
    }

    fn update_name(&{mut name} mut self, new_name: String) {
        self.name = new_name;
    }

    // Resource field is NOT borrowed, so it can still be dropped normally
    fn use_other_fields(&{counter, name} self) -> (usize, &str) { //~ ERROR view-typed functions cannot return references
        (self.counter, &self.name)
    }
}

// =============================================================================
// Test 3: Lifetime Bounds - References Returned from View Functions
// =============================================================================

struct Container {
    data: Vec<String>,
    metadata: String,
    index: usize,
}

impl Container {
    // Return reference with lifetime tied to self
    fn get_data_ref(&{data} self, idx: usize) -> Option<&String> {
        self.data.get(idx)
    }

    // Multiple references from same view
    fn get_first_last(&{data} self) -> (Option<&String>, Option<&String>) {
        (self.data.first(), self.data.last())
    }

    // Reference to field itself
    fn get_metadata_ref(&{metadata} self) -> &str { //~ ERROR view-typed functions cannot return references
        &self.metadata
    }

    // Mutable reference with lifetime bound
    fn get_data_mut(&{mut data} mut self, idx: usize) -> Option<&mut String> {
        self.data.get_mut(idx)
    }

    // Multiple mutable refs to different fields (not simultaneously!)
    fn get_metadata_mut(&{mut metadata} mut self) -> &mut String { //~ ERROR view-typed functions cannot return references
        &mut self.metadata
    }
}

// =============================================================================
// Test 4: Explicit Lifetime Parameters
// =============================================================================

struct WithLifetime<'a> {
    borrowed: &'a str,
    owned: String,
    counter: usize,
}

impl<'a> WithLifetime<'a> {
    fn get_borrowed(&{borrowed} self) -> &'a str { //~ ERROR view-typed functions cannot return references
        self.borrowed
    }

    fn get_owned_ref(&{owned} self) -> &str { //~ ERROR view-typed functions cannot return references
        &self.owned
    }

    fn get_counter(&{counter} self) -> usize {
        self.counter
    }

    fn modify_owned(&{mut owned} mut self, suffix: &str) {
        self.owned.push_str(suffix);
    }

    fn modify_counter(&{mut counter} mut self) {
        self.counter += 1;
    }
}

// =============================================================================
// Test 5: RAII Guard Pattern
// =============================================================================

struct Guard<'a> {
    lock: &'a RefCell<bool>,
}

impl<'a> Guard<'a> {
    fn new(lock: &'a RefCell<bool>) -> Self {
        *lock.borrow_mut() = true;
        Guard { lock }
    }
}

impl<'a> Drop for Guard<'a> {
    fn drop(&mut self) {
        *self.lock.borrow_mut() = false;
    }
}

struct WithGuard {
    lock: RefCell<bool>,
    data: Vec<i32>,
}

impl WithGuard {
    fn is_locked(&{lock} self) -> bool {
        *self.lock.borrow()
    }

    fn create_guard(&{lock} self) -> Guard<'_> {
        Guard::new(&self.lock)
    }

    fn modify_data(&{mut data} mut self, value: i32) {
        self.data.push(value);
    }
}

// =============================================================================
// Test 6: Early Drop via std::mem::drop
// =============================================================================

struct EarlyDroppable {
    name: String,
}

impl Drop for EarlyDroppable {
    fn drop(&mut self) {
        // Explicit drop
    }
}

struct WithEarlyDrop {
    droppable: EarlyDroppable,
    counter: usize,
    data: Vec<i32>,
}

impl WithEarlyDrop {
    fn increment(&{mut counter} mut self) {
        self.counter += 1;
    }

    fn use_data(&{mut data} mut self) {
        self.data.push(42);
    }

    // Can still access other fields while droppable exists
    fn access_others(&{counter, data} self) -> (usize, usize) {
        (self.counter, self.data.len())
    }
}

// =============================================================================
// Test 7: Multiple Lifetimes
// =============================================================================

struct TwoRefs<'a, 'b> {
    first: &'a str,
    second: &'b str,
    owned: String,
}

impl<'a, 'b> TwoRefs<'a, 'b> {
    fn get_first(&{first} self) -> &'a str { //~ ERROR view-typed functions cannot return references
        self.first
    }

    fn get_second(&{second} self) -> &'b str { //~ ERROR view-typed functions cannot return references
        self.second
    }

    fn get_both(&{first, second} self) -> (&'a str, &'b str) { //~ ERROR view-typed functions cannot return references
        (self.first, self.second)
    }

    fn get_owned(&{owned} self) -> &str { //~ ERROR view-typed functions cannot return references
        &self.owned
    }

    fn concat(&{first, second, owned} self) -> String {
        format!("{}{}{}", self.first, self.second, self.owned)
    }
}

// =============================================================================
// Test 8: Nested Drop Order
// =============================================================================

struct Inner {
    value: i32,
}

impl Drop for Inner {
    fn drop(&mut self) {
        // Inner dropped
    }
}

struct Outer {
    inner: Inner,
    name: String,
}

impl Drop for Outer {
    fn drop(&mut self) {
        // Outer dropped (then inner)
    }
}

struct WithNested {
    outer: Outer,
    counter: usize,
}

impl WithNested {
    fn get_counter(&{counter} self) -> usize {
        self.counter
    }

    fn increment(&{mut counter} mut self) {
        self.counter += 1;
    }

    // Not accessing outer, so drop behavior unaffected
}

// =============================================================================
// Test 9: References with Different Mutabilities
// =============================================================================

struct Mixed {
    immut_field: Vec<i32>,
    mut_field: Vec<String>,
}

impl Mixed {
    fn get_immut(&{immut_field} self) -> &[i32] { //~ ERROR view-typed functions cannot return references
        &self.immut_field
    }

    fn get_mut(&{mut mut_field} mut self) -> &mut Vec<String> { //~ ERROR view-typed functions cannot return references
        &mut self.mut_field
    }

    fn iter_immut(&{immut_field} self) -> impl Iterator<Item = &i32> {
        self.immut_field.iter()
    }

    fn sum_immut(&{immut_field} self) -> i32 {
        self.immut_field.iter().sum()
    }
}

// =============================================================================
// Test 10: Lifetime Elision Works Correctly
// =============================================================================

struct Elided {
    text: String,
    numbers: Vec<i32>,
}

impl Elided {
    // Lifetime elided - should be tied to &self
    fn first_line(&{text} self) -> &str { //~ ERROR view-typed functions cannot return references
        self.text.lines().next().unwrap_or("")
    }

    fn first_number(&{numbers} self) -> Option<&i32> {
        self.numbers.first()
    }

    fn slice_numbers(&{numbers} self, start: usize, end: usize) -> &[i32] { //~ ERROR view-typed functions cannot return references
        &self.numbers[start..end]
    }
}

// =============================================================================
// Test 11: Drop with Generics
// =============================================================================

struct GenericDrop<T> {
    value: T,
}

impl<T> Drop for GenericDrop<T> {
    fn drop(&mut self) {
        // Generic drop
    }
}

struct WithGenericDrop<T> {
    drop_field: GenericDrop<T>,
    counter: usize,
}

impl<T> WithGenericDrop<T> {
    fn get_counter(&{counter} self) -> usize {
        self.counter
    }

    fn increment(&{mut counter} mut self) {
        self.counter += 1;
    }
}

// =============================================================================
// Test 12: Real-World Pattern - Connection Guard
// =============================================================================

struct Connection {
    id: usize,
    active: bool,
}

impl Drop for Connection {
    fn drop(&mut self) {
        // Close connection
        self.active = false;
    }
}

struct ConnectionPool {
    connections: Vec<Connection>,
    stats: RefCell<PoolStats>,
}

struct PoolStats {
    total_requests: usize,
    active_connections: usize,
}

impl ConnectionPool {
    fn increment_requests(&{stats} self) {
        self.stats.borrow_mut().total_requests += 1;
    }

    fn get_requests(&{stats} self) -> usize {
        self.stats.borrow().total_requests
    }

    fn connection_count(&{connections} self) -> usize {
        self.connections.len()
    }

    // Stats and connections are separate - can be borrowed independently
    fn get_stats_while_counting(&{stats, connections} self) -> (usize, usize) {
        (self.stats.borrow().total_requests, self.connections.len())
    }
}

// =============================================================================
// Main: Test Drop and Lifetime Scenarios
// =============================================================================

fn main() {
    // Test 1: Basic drop tracking
    {
        let log = Rc::new(RefCell::new(Vec::new()));
        {
            let wd = WithDrop {
                tracker_a: DropTracker { id: 1, log: Rc::clone(&log) },
                tracker_b: DropTracker { id: 2, log: Rc::clone(&log) },
                value: 42,
            };
            assert_eq!(wd.use_tracker_a(), 1);
            assert_eq!(wd.use_tracker_b(), 2);
            assert_eq!(wd.use_value(), 42);
            // Drops happen here
        }
        let dropped = log.borrow();
        assert_eq!(dropped.len(), 2);
        // Order: fields dropped in declaration order (a, then b)
        assert!(dropped.contains(&String::from("dropped_1")));
        assert!(dropped.contains(&String::from("dropped_2")));
    }

    // Test 2: Drop with mutable borrows
    {
        let mut wr = WithResource {
            resource: Resource { data: vec![1, 2, 3] },
            counter: 0,
            name: String::from("test"),
        };
        wr.increment_counter();
        assert_eq!(wr.get_counter(), 1);
        wr.update_name(String::from("updated"));
        // Resource not borrowed, drops normally
    }

    // Test 3: References from view functions
    {
        let cont = Container {
            data: vec![String::from("first"), String::from("second")],
            metadata: String::from("meta"),
            index: 0,
        };
        let data_ref = cont.get_data_ref(0);
        assert_eq!(data_ref, Some(&String::from("first")));
        let (first, last) = cont.get_first_last();
        assert_eq!(first, Some(&String::from("first")));
        assert_eq!(last, Some(&String::from("second")));
        let meta = cont.get_metadata_ref();
        assert_eq!(meta, "meta");
    }

    // Test 4: Explicit lifetimes
    {
        let borrowed_str = "borrowed";
        let wl = WithLifetime {
            borrowed: borrowed_str,
            owned: String::from("owned"),
            counter: 0,
        };
        assert_eq!(wl.get_borrowed(), "borrowed");
        assert_eq!(wl.get_owned_ref(), "owned");
        assert_eq!(wl.get_counter(), 0);
    }

    // Test 5: RAII guard
    {
        let wg = WithGuard {
            lock: RefCell::new(false),
            data: vec![],
        };
        assert!(!wg.is_locked());
        {
            let _guard = wg.create_guard();
            assert!(wg.is_locked());
        }
        assert!(!wg.is_locked()); // Guard dropped, lock released
    }

    // Test 6: Early drop
    {
        let mut wed = WithEarlyDrop {
            droppable: EarlyDroppable { name: String::from("drop me") },
            counter: 0,
            data: vec![],
        };
        wed.increment();
        wed.use_data();
        let (count, len) = wed.access_others();
        assert_eq!(count, 1);
        assert_eq!(len, 1);
    }

    // Test 7: Multiple lifetimes
    {
        let first_str = "first";
        let second_str = "second";
        let tr = TwoRefs {
            first: first_str,
            second: second_str,
            owned: String::from("owned"),
        };
        assert_eq!(tr.get_first(), "first");
        assert_eq!(tr.get_second(), "second");
        let (f, s) = tr.get_both();
        assert_eq!(f, "first");
        assert_eq!(s, "second");
        let concat = tr.concat();
        assert_eq!(concat, "firstsecondowned");
    }

    // Test 8: Nested drop order
    {
        let wn = WithNested {
            outer: Outer {
                inner: Inner { value: 42 },
                name: String::from("outer"),
            },
            counter: 0,
        };
        assert_eq!(wn.get_counter(), 0);
        // Drops: wn, then outer, then inner
    }

    // Test 9: Mixed mutabilities
    {
        let mut mix = Mixed {
            immut_field: vec![1, 2, 3],
            mut_field: vec![String::from("a")],
        };
        let slice = mix.get_immut();
        assert_eq!(slice.len(), 3);
        let sum = mix.sum_immut();
        assert_eq!(sum, 6);
        let mut_vec = mix.get_mut();
        mut_vec.push(String::from("b"));
        assert_eq!(mix.mut_field.len(), 2);
    }

    // Test 10: Lifetime elision
    {
        let elided = Elided {
            text: String::from("line1\nline2"),
            numbers: vec![10, 20, 30],
        };
        let line = elided.first_line();
        assert_eq!(line, "line1");
        let first = elided.first_number();
        assert_eq!(first, Some(&10));
        let slice = elided.slice_numbers(0, 2);
        assert_eq!(slice, &[10, 20]);
    }

    // Test 11: Generic drop
    {
        let mut wgd: WithGenericDrop<i32> = WithGenericDrop {
            drop_field: GenericDrop { value: 42 },
            counter: 0,
        };
        assert_eq!(wgd.get_counter(), 0);
        wgd.increment();
        assert_eq!(wgd.get_counter(), 1);
    }

    // Test 12: Connection pool
    {
        let pool = ConnectionPool {
            connections: vec![
                Connection { id: 1, active: true },
                Connection { id: 2, active: true },
            ],
            stats: RefCell::new(PoolStats {
                total_requests: 0,
                active_connections: 2,
            }),
        };
        pool.increment_requests();
        pool.increment_requests();
        assert_eq!(pool.get_requests(), 2);
        assert_eq!(pool.connection_count(), 2);
        let (reqs, conns) = pool.get_stats_while_counting();
        assert_eq!(reqs, 2);
        assert_eq!(conns, 2);
    }

    println!("✓ All Drop and lifetime tests passed!");
}
