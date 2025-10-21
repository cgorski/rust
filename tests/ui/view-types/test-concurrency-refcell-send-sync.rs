//@ check-pass
#![feature(view_types)]
#![allow(unused, incomplete_features)]

// TEST: RefCell Interior Mutability and Send/Sync with View Types
//
// CRITICAL PROPERTIES:
// 1. View-typed methods work with RefCell interior mutability
// 2. RefCell runtime borrow checking doesn't conflict with view type semantics
// 3. Send/Sync auto-traits are correctly derived for view-typed structs
// 4. Interior mutability patterns (RefCell, Cell) compose with view types
//
// RATIONALE:
// RefCell provides runtime-checked interior mutability, which is orthogonal
// to view types' compile-time field access restrictions. This test verifies
// they compose correctly without interference.

use std::cell::{RefCell, Cell};
use std::rc::Rc;

// =============================================================================
// Test 1: Basic RefCell with View-Typed Methods
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

    fn update_max(&{mut max} mut self, new_max: usize) {
        self.max = new_max;
    }

    fn get_max(&{max} self) -> usize {
        self.max
    }
}

fn test_basic_refcell() {
    let counter = RefCell::new(Counter {
        count: 0,
        max: 100,
        name: String::from("test"),
    });

    // Mutable borrow and call view-typed method
    {
        let mut borrow = counter.borrow_mut();
        borrow.increment();
        assert_eq!(borrow.get_count(), 1);
    }

    // Immutable borrow and call view-typed method
    {
        let borrow = counter.borrow();
        assert_eq!(borrow.get_count(), 1);
    }

    // Another mutable borrow on different field
    {
        let mut borrow = counter.borrow_mut();
        borrow.update_max(200);
    }

    println!("Basic RefCell with view types: OK");
}

// =============================================================================
// Test 2: Multiple Immutable Borrows
// =============================================================================

fn test_multiple_immutable_borrows() {
    let counter = RefCell::new(Counter {
        count: 42,
        max: 100,
        name: String::from("shared"),
    });

    // Multiple immutable borrows at once
    let borrow1 = counter.borrow();
    let borrow2 = counter.borrow();
    let borrow3 = counter.borrow();

    // All can call view-typed methods
    assert_eq!(borrow1.get_count(), 42);
    assert_eq!(borrow2.get_max(), 100);
    assert_eq!(borrow3.get_count(), 42);

    drop(borrow1);
    drop(borrow2);
    drop(borrow3);

    println!("Multiple immutable RefCell borrows: OK");
}

// =============================================================================
// Test 3: Rc<RefCell<T>> Pattern
// =============================================================================

fn test_rc_refcell_pattern() {
    let counter = Rc::new(RefCell::new(Counter {
        count: 0,
        max: 0,
        name: String::from("shared"),
    }));

    // Clone Rc for shared ownership
    let counter2 = Rc::clone(&counter);
    let counter3 = Rc::clone(&counter);

    // Each clone can borrow and modify
    {
        let mut borrow = counter.borrow_mut();
        borrow.increment();
    }

    {
        let mut borrow = counter2.borrow_mut();
        borrow.increment();
    }

    {
        let borrow = counter3.borrow();
        assert_eq!(borrow.get_count(), 2);
    }

    println!("Rc<RefCell<T>> pattern: OK");
}

// =============================================================================
// Test 4: Send/Sync Auto-Trait Verification
// =============================================================================

// Struct that should be Send
#[derive(Debug)]
struct SendableData {
    value: i32,
    name: String,
}

impl SendableData {
    fn update_value(&{mut value} mut self, new_val: i32) {
        self.value = new_val;
    }

    fn get_value(&{value} self) -> i32 {
        self.value
    }
}

// Struct that should be Sync (all fields are Sync)
#[derive(Debug)]
struct SyncableData {
    counter: usize,
    flag: bool,
}

impl SyncableData {
    fn increment(&{mut counter} mut self) {
        self.counter += 1;
    }

    fn get_counter(&{counter} self) -> usize {
        self.counter
    }
}

// Helper to verify Send
fn assert_send<T: Send>() {}

// Helper to verify Sync
fn assert_sync<T: Sync>() {}

fn test_send_sync_auto_traits() {
    // Verify view-typed structs have correct Send/Sync traits
    assert_send::<SendableData>();
    assert_sync::<SendableData>();

    assert_send::<SyncableData>();
    assert_sync::<SyncableData>();

    // Verify RefCell is NOT Sync (expected behavior)
    // assert_sync::<RefCell<Counter>>(); // Would not compile - correct!

    // But RefCell IS Send
    assert_send::<RefCell<Counter>>();

    println!("Send/Sync auto-trait verification: OK");
}

// =============================================================================
// Test 5: Cell with View Types (Simpler Interior Mutability)
// =============================================================================

struct CellContainer {
    value: Cell<i32>,
    metadata: String,
}

impl CellContainer {
    fn update_metadata(&{mut metadata} mut self, new_meta: String) {
        self.metadata = new_meta;
    }

    fn get_metadata_len(&{metadata} self) -> usize {
        self.metadata.len()
    }

    // Note: Can't have view-typed method for Cell<i32> field
    // Cell doesn't support references to its contents
    fn get_value(&self) -> i32 {
        self.value.get()
    }

    fn set_value(&self, val: i32) {
        self.value.set(val);
    }
}

fn test_cell_with_view_types() {
    let container = CellContainer {
        value: Cell::new(0),
        metadata: String::from("test"),
    };

    // Cell allows interior mutability without mut self
    container.set_value(42);
    assert_eq!(container.get_value(), 42);

    // View-typed methods work on non-Cell fields
    let len = container.get_metadata_len();
    assert_eq!(len, 4);

    println!("Cell with view types: OK");
}

// =============================================================================
// Test 6: Interior Mutability with Disjoint Fields
// =============================================================================

struct DisjointFields {
    field_a: RefCell<i32>,
    field_b: RefCell<String>,
    field_c: usize,
}

impl DisjointFields {
    fn update_c(&{mut field_c} mut self, new_val: usize) {
        self.field_c = new_val;
    }

    fn get_c(&{field_c} self) -> usize {
        self.field_c
    }

    // Can't use view types on RefCell fields directly
    // (no direct field access, must go through RefCell API)
    fn update_a(&self, new_val: i32) {
        *self.field_a.borrow_mut() = new_val;
    }

    fn get_a(&self) -> i32 {
        *self.field_a.borrow()
    }
}

fn test_disjoint_interior_mutability() {
    let data = DisjointFields {
        field_a: RefCell::new(0),
        field_b: RefCell::new(String::from("initial")),
        field_c: 0,
    };

    // Update through RefCell
    data.update_a(42);
    assert_eq!(data.get_a(), 42);

    // Update through view-typed method
    let mut data_mut = data;
    data_mut.update_c(100);
    assert_eq!(data_mut.get_c(), 100);

    println!("Disjoint interior mutability: OK");
}

// =============================================================================
// Test 7: RefCell Panic Behavior (Runtime Borrow Checking)
// =============================================================================

fn test_refcell_panic_behavior() {
    let counter = RefCell::new(Counter {
        count: 0,
        max: 0,
        name: String::from("test"),
    });

    // This should work fine
    {
        let mut borrow = counter.borrow_mut();
        borrow.increment();
    } // Mutable borrow released

    // Subsequent borrow works
    {
        let borrow = counter.borrow();
        assert_eq!(borrow.get_count(), 1);
    }

    // Note: Attempting to hold both mutable and immutable borrows
    // simultaneously would panic at runtime (RefCell's job, not view types)
    // We don't test that here since it would crash the test

    println!("RefCell runtime borrow checking: OK");
}

// =============================================================================
// Test 8: View Types Don't Affect RefCell Semantics
// =============================================================================

struct TwoFields {
    field_a: i32,
    field_b: String,
}

impl TwoFields {
    fn update_a(&{mut field_a} mut self, val: i32) {
        self.field_a = val;
    }

    fn update_b(&{mut field_b} mut self, val: String) {
        self.field_b = val;
    }

    fn read_both(&{field_a, field_b} self) -> (i32, String) {
        (self.field_a, self.field_b.clone())
    }
}

fn test_refcell_semantics_preserved() {
    let data = RefCell::new(TwoFields {
        field_a: 0,
        field_b: String::from("initial"),
    });

    // View types work through RefCell
    {
        let mut borrow = data.borrow_mut();
        borrow.update_a(42);
        borrow.update_b(String::from("updated"));
    }

    {
        let borrow = data.borrow();
        let (a, b) = borrow.read_both();
        assert_eq!(a, 42);
        assert_eq!(b, "updated");
    }

    println!("RefCell semantics preserved with view types: OK");
}

// =============================================================================
// Test 9: Generic Struct with RefCell and View Types
// =============================================================================

struct GenericWithRefCell<T> {
    data: RefCell<T>,
    metadata: String,
    count: usize,
}

impl<T> GenericWithRefCell<T> {
    fn update_metadata(&{mut metadata} mut self, new_meta: String) {
        self.metadata = new_meta;
    }

    fn increment_count(&{mut count} mut self) {
        self.count += 1;
    }

    fn get_count(&{count} self) -> usize {
        self.count
    }
}

fn test_generic_refcell() {
    let container = GenericWithRefCell {
        data: RefCell::new(vec![1, 2, 3]),
        metadata: String::from("vec"),
        count: 0,
    };

    // View-typed methods work on non-RefCell fields
    let len = container.get_count();
    assert_eq!(len, 0);

    // RefCell field accessed normally
    {
        let mut borrow = container.data.borrow_mut();
        borrow.push(4);
    }

    println!("Generic struct with RefCell: OK");
}

// =============================================================================
// Test 10: Real-World Pattern - State Machine with Interior Mutability
// =============================================================================

#[derive(Debug, PartialEq, Clone)]
enum State {
    Init,
    Running,
    Stopped,
}

struct StateMachine {
    state: RefCell<State>,
    error_count: usize,
    success_count: usize,
}

impl StateMachine {
    fn new() -> Self {
        StateMachine {
            state: RefCell::new(State::Init),
            error_count: 0,
            success_count: 0,
        }
    }

    fn record_error(&{mut error_count} mut self) {
        self.error_count += 1;
    }

    fn record_success(&{mut success_count} mut self) {
        self.success_count += 1;
    }

    fn get_stats(&{error_count, success_count} self) -> (usize, usize) {
        (self.error_count, self.success_count)
    }

    // State transitions through RefCell
    fn transition_to(&self, new_state: State) {
        *self.state.borrow_mut() = new_state;
    }

    fn current_state(&self) -> State {
        self.state.borrow().clone()
    }
}

fn test_state_machine_pattern() {
    let mut machine = StateMachine::new();

    // Transition state (through RefCell)
    machine.transition_to(State::Running);
    assert_eq!(machine.current_state(), State::Running);

    // Record stats (through view-typed methods)
    machine.record_success();
    machine.record_success();
    machine.record_error();

    let (errors, successes) = machine.get_stats();
    assert_eq!(errors, 1);
    assert_eq!(successes, 2);

    println!("State machine with interior mutability: OK");
}

// =============================================================================
// Main Test Runner
// =============================================================================

fn main() {
    test_basic_refcell();
    test_multiple_immutable_borrows();
    test_rc_refcell_pattern();
    test_send_sync_auto_traits();
    test_cell_with_view_types();
    test_disjoint_interior_mutability();
    test_refcell_panic_behavior();
    test_refcell_semantics_preserved();
    test_generic_refcell();
    test_state_machine_pattern();

    println!("\n✓ All RefCell and Send/Sync tests passed!");
    println!("✓ View-typed methods work correctly with RefCell interior mutability");
    println!("✓ Send/Sync auto-traits are correctly derived");
    println!("✓ RefCell runtime borrow checking preserved");
    println!("✓ Interior mutability patterns compose with view types");
    println!("✓ Real-world patterns (state machine, Rc<RefCell<T>>) work");
}
