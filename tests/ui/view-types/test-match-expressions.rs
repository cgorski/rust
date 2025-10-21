//@ check-pass
#![feature(view_types)]
#![allow(unused, incomplete_features)]

// TEST: Match Expressions with View Types
//
// PURPOSE: Verify that match expressions work correctly with view-typed methods.
// Test pattern matching, destructuring, guards, and various match scenarios.
//
// RATIONALE:
// Match expressions are fundamental to Rust. Users will naturally combine them
// with view types when:
// - State machines with different states accessing different fields
// - Option/Result handling in methods with view specs
// - Enum variants with different field access patterns
// - Conditional logic based on field values
//
// This tests that view types don't interfere with pattern matching and that
// match arms can call view-typed methods appropriately.

// =============================================================================
// Test 1: Basic Match with View-Typed Method Calls
// =============================================================================

#[derive(Debug, PartialEq)]
enum State {
    Active,
    Paused,
    Stopped,
}

struct StateMachine {
    state: State,
    counter: u32,
    data: Vec<i32>,
}

impl StateMachine {
    fn increment_counter(&{mut counter} mut self) {
        self.counter += 1;
    }

    fn add_data(&{mut data} mut self, value: i32) {
        self.data.push(value);
    }

    fn reset_counter(&{mut counter} mut self) {
        self.counter = 0;
    }

    // Match on state, call different view-typed methods per arm
    fn process(&mut self, value: i32) {
        match self.state {
            State::Active => {
                self.increment_counter();
                self.add_data(value);
            }
            State::Paused => {
                self.add_data(value);
            }
            State::Stopped => {
                self.reset_counter();
            }
        }
    }
}

// =============================================================================
// Test 2: Match with Pattern Destructuring
// =============================================================================

enum Message {
    Increment(u32),
    Decrement(u32),
    Reset,
    SetData(Vec<String>),
}

struct Counter {
    count: u32,
    data: Vec<String>,
}

impl Counter {
    fn increment(&{mut count} mut self, amount: u32) {
        self.count += amount;
    }

    fn decrement(&{mut count} mut self, amount: u32) {
        self.count = self.count.saturating_sub(amount);
    }

    fn reset(&{mut count} mut self) {
        self.count = 0;
    }

    fn set_data(&{mut data} mut self, new_data: Vec<String>) {
        self.data = new_data;
    }

    // Match with destructuring, call view-typed methods
    fn handle_message(&mut self, msg: Message) {
        match msg {
            Message::Increment(amount) => self.increment(amount),
            Message::Decrement(amount) => self.decrement(amount),
            Message::Reset => self.reset(),
            Message::SetData(data) => self.set_data(data),
        }
    }
}

// =============================================================================
// Test 3: Match on Option with View Types
// =============================================================================

struct OptionalData {
    value: Option<i32>,
    cache: Vec<i32>,
    error_count: u32,
}

impl OptionalData {
    fn add_to_cache(&{mut cache} mut self, value: i32) {
        self.cache.push(value);
    }

    fn increment_errors(&{mut error_count} mut self) {
        self.error_count += 1;
    }

    // Match on Option field, call view-typed methods
    fn process(&mut self) {
        match self.value {
            Some(v) => {
                self.add_to_cache(v);
            }
            None => {
                self.increment_errors();
            }
        }
    }

    // Match with binding
    fn process_with_transform(&mut self) {
        match self.value {
            Some(v) if v > 0 => {
                self.add_to_cache(v * 2);
            }
            Some(v) => {
                self.add_to_cache(v);
            }
            None => {
                self.increment_errors();
            }
        }
    }
}

// =============================================================================
// Test 4: Match on Result with View Types
// =============================================================================

struct ResultHandler {
    success_count: u32,
    error_count: u32,
    results: Vec<i32>,
}

impl ResultHandler {
    fn increment_success(&{mut success_count} mut self) {
        self.success_count += 1;
    }

    fn increment_errors(&{mut error_count} mut self) {
        self.error_count += 1;
    }

    fn add_result(&{mut results} mut self, value: i32) {
        self.results.push(value);
    }

    // Match on Result, call different view-typed methods
    fn handle_result(&mut self, res: Result<i32, String>) {
        match res {
            Ok(value) => {
                self.increment_success();
                self.add_result(value);
            }
            Err(_) => {
                self.increment_errors();
            }
        }
    }
}

// =============================================================================
// Test 5: Match Guards with View Types
// =============================================================================

struct GuardTest {
    threshold: u32,
    low_count: u32,
    high_count: u32,
    equal_count: u32,
}

impl GuardTest {
    fn increment_low(&{mut low_count} mut self) {
        self.low_count += 1;
    }

    fn increment_high(&{mut high_count} mut self) {
        self.high_count += 1;
    }

    fn increment_equal(&{mut equal_count} mut self) {
        self.equal_count += 1;
    }

    // Match with guards calling view-typed methods
    fn categorize(&mut self, value: u32) {
        match value {
            v if v < self.threshold => self.increment_low(),
            v if v > self.threshold => self.increment_high(),
            _ => self.increment_equal(),
        }
    }
}

// =============================================================================
// Test 6: Nested Match Expressions
// =============================================================================

enum OuterEnum {
    Case1(InnerEnum),
    Case2(InnerEnum),
}

enum InnerEnum {
    A(i32),
    B(i32),
}

struct NestedMatcher {
    case1_a: u32,
    case1_b: u32,
    case2_a: u32,
    case2_b: u32,
}

impl NestedMatcher {
    fn increment_case1_a(&{mut case1_a} mut self) {
        self.case1_a += 1;
    }

    fn increment_case1_b(&{mut case1_b} mut self) {
        self.case1_b += 1;
    }

    fn increment_case2_a(&{mut case2_a} mut self) {
        self.case2_a += 1;
    }

    fn increment_case2_b(&{mut case2_b} mut self) {
        self.case2_b += 1;
    }

    // Nested match calling different view-typed methods
    fn process_nested(&mut self, outer: OuterEnum) {
        match outer {
            OuterEnum::Case1(inner) => match inner {
                InnerEnum::A(_) => self.increment_case1_a(),
                InnerEnum::B(_) => self.increment_case1_b(),
            },
            OuterEnum::Case2(inner) => match inner {
                InnerEnum::A(_) => self.increment_case2_a(),
                InnerEnum::B(_) => self.increment_case2_b(),
            },
        }
    }
}

// =============================================================================
// Test 7: Match with Multiple Bindings
// =============================================================================

enum Command {
    Move { x: i32, y: i32 },
    Scale { factor: f32 },
    Reset,
}

struct Transform {
    x: i32,
    y: i32,
    scale: f32,
}

impl Transform {
    fn move_to(&{mut x, mut y} mut self, new_x: i32, new_y: i32) {
        self.x = new_x;
        self.y = new_y;
    }

    fn set_scale(&{mut scale} mut self, factor: f32) {
        self.scale = factor;
    }

    fn reset(&{mut x, mut y, mut scale} mut self) {
        self.x = 0;
        self.y = 0;
        self.scale = 1.0;
    }

    // Match with struct destructuring
    fn execute(&mut self, cmd: Command) {
        match cmd {
            Command::Move { x, y } => self.move_to(x, y),
            Command::Scale { factor } => self.set_scale(factor),
            Command::Reset => self.reset(),
        }
    }
}

// =============================================================================
// Test 8: Match in Iterator Chain with View Types
// =============================================================================

struct Processor {
    success: u32,
    failure: u32,
    results: Vec<i32>,
}

impl Processor {
    fn increment_success(&{mut success} mut self) {
        self.success += 1;
    }

    fn increment_failure(&{mut failure} mut self) {
        self.failure += 1;
    }

    fn add_result(&{mut results} mut self, value: i32) {
        self.results.push(value);
    }

    // Match inside iterator closure with view-typed methods
    fn process_results(&mut self, results: Vec<Result<i32, String>>) {
        results.into_iter().for_each(|res| match res {
            Ok(v) => {
                self.increment_success();
                self.add_result(v);
            }
            Err(_) => {
                self.increment_failure();
            }
        });
    }
}

// =============================================================================
// Test 9: Match with Reference Patterns
// =============================================================================

struct RefMatcher {
    none_count: u32,
    some_count: u32,
    values: Vec<i32>,
}

impl RefMatcher {
    fn increment_none(&{mut none_count} mut self) {
        self.none_count += 1;
    }

    fn increment_some(&{mut some_count} mut self) {
        self.some_count += 1;
    }

    fn add_value(&{mut values} mut self, value: i32) {
        self.values.push(value);
    }

    // Match on references
    fn process_option_ref(&mut self, opt: &Option<i32>) {
        match opt {
            Some(v) => {
                self.increment_some();
                self.add_value(*v);
            }
            None => {
                self.increment_none();
            }
        }
    }
}

// =============================================================================
// Test 10: Real-World State Machine Pattern
// =============================================================================

#[derive(Debug, Clone, Copy)]
enum ConnectionState {
    Disconnected,
    Connecting,
    Connected,
    Error,
}

struct Connection {
    state: ConnectionState,
    retry_count: u32,
    success_count: u32,
    error_count: u32,
    messages: Vec<String>,
}

impl Connection {
    fn increment_retries(&{mut retry_count} mut self) {
        self.retry_count += 1;
    }

    fn increment_success(&{mut success_count} mut self) {
        self.success_count += 1;
    }

    fn increment_errors(&{mut error_count} mut self) {
        self.error_count += 1;
    }

    fn reset_retries(&{mut retry_count} mut self) {
        self.retry_count = 0;
    }

    fn add_message(&{mut messages} mut self, msg: String) {
        self.messages.push(msg);
    }

    fn change_state(&{mut state} mut self, new_state: ConnectionState) {
        self.state = new_state;
    }

    // State machine with match
    fn handle_event(&mut self, event: &str) {
        match (self.state, event) {
            (ConnectionState::Disconnected, "connect") => {
                self.change_state(ConnectionState::Connecting);
                self.increment_retries();
            }
            (ConnectionState::Connecting, "success") => {
                self.change_state(ConnectionState::Connected);
                self.increment_success();
                self.reset_retries();
            }
            (ConnectionState::Connecting, "failure") => {
                if self.retry_count < 3 {
                    self.increment_retries();
                } else {
                    self.change_state(ConnectionState::Error);
                    self.increment_errors();
                }
            }
            (ConnectionState::Connected, "disconnect") => {
                self.change_state(ConnectionState::Disconnected);
                self.add_message("Disconnected".to_string());
            }
            (ConnectionState::Error, "reset") => {
                self.change_state(ConnectionState::Disconnected);
                self.reset_retries();
            }
            _ => {
                // Ignore invalid state transitions
            }
        }
    }
}

// =============================================================================
// Main Test Driver
// =============================================================================

fn main() {
    // Test 1: Basic match
    let mut sm = StateMachine {
        state: State::Active,
        counter: 0,
        data: vec![],
    };
    sm.process(10);
    assert_eq!(sm.counter, 1);
    assert_eq!(sm.data, vec![10]);

    sm.state = State::Paused;
    sm.process(20);
    assert_eq!(sm.counter, 1); // Not incremented
    assert_eq!(sm.data, vec![10, 20]);

    sm.state = State::Stopped;
    sm.process(30);
    assert_eq!(sm.counter, 0); // Reset
    println!("✓ Basic match with view types works");

    // Test 2: Pattern destructuring
    let mut counter = Counter {
        count: 0,
        data: vec![],
    };
    counter.handle_message(Message::Increment(5));
    assert_eq!(counter.count, 5);
    counter.handle_message(Message::Decrement(2));
    assert_eq!(counter.count, 3);
    counter.handle_message(Message::Reset);
    assert_eq!(counter.count, 0);
    println!("✓ Pattern destructuring with view types works");

    // Test 3: Option matching
    let mut opt_data = OptionalData {
        value: Some(42),
        cache: vec![],
        error_count: 0,
    };
    opt_data.process();
    assert_eq!(opt_data.cache, vec![42]);
    assert_eq!(opt_data.error_count, 0);

    opt_data.value = None;
    opt_data.process();
    assert_eq!(opt_data.error_count, 1);
    println!("✓ Option matching with view types works");

    // Test 4: Result matching
    let mut handler = ResultHandler {
        success_count: 0,
        error_count: 0,
        results: vec![],
    };
    handler.handle_result(Ok(100));
    assert_eq!(handler.success_count, 1);
    assert_eq!(handler.results, vec![100]);
    handler.handle_result(Err("error".to_string()));
    assert_eq!(handler.error_count, 1);
    println!("✓ Result matching with view types works");

    // Test 5: Match guards
    let mut guard_test = GuardTest {
        threshold: 50,
        low_count: 0,
        high_count: 0,
        equal_count: 0,
    };
    guard_test.categorize(25);
    guard_test.categorize(75);
    guard_test.categorize(50);
    assert_eq!(guard_test.low_count, 1);
    assert_eq!(guard_test.high_count, 1);
    assert_eq!(guard_test.equal_count, 1);
    println!("✓ Match guards with view types work");

    // Test 6: Nested match
    let mut nested = NestedMatcher {
        case1_a: 0,
        case1_b: 0,
        case2_a: 0,
        case2_b: 0,
    };
    nested.process_nested(OuterEnum::Case1(InnerEnum::A(1)));
    nested.process_nested(OuterEnum::Case1(InnerEnum::B(2)));
    nested.process_nested(OuterEnum::Case2(InnerEnum::A(3)));
    assert_eq!(nested.case1_a, 1);
    assert_eq!(nested.case1_b, 1);
    assert_eq!(nested.case2_a, 1);
    println!("✓ Nested match with view types works");

    // Test 7: Multiple bindings
    let mut transform = Transform {
        x: 0,
        y: 0,
        scale: 1.0,
    };
    transform.execute(Command::Move { x: 10, y: 20 });
    assert_eq!(transform.x, 10);
    assert_eq!(transform.y, 20);
    transform.execute(Command::Scale { factor: 2.0 });
    assert_eq!(transform.scale, 2.0);
    println!("✓ Multiple bindings in match work");

    // Test 8: Match in iterators
    let mut proc = Processor {
        success: 0,
        failure: 0,
        results: vec![],
    };
    proc.process_results(vec![Ok(1), Err("e".to_string()), Ok(2)]);
    assert_eq!(proc.success, 2);
    assert_eq!(proc.failure, 1);
    assert_eq!(proc.results, vec![1, 2]);
    println!("✓ Match in iterators with view types works");

    // Test 9: Reference patterns
    let mut ref_matcher = RefMatcher {
        none_count: 0,
        some_count: 0,
        values: vec![],
    };
    ref_matcher.process_option_ref(&Some(42));
    ref_matcher.process_option_ref(&None);
    assert_eq!(ref_matcher.some_count, 1);
    assert_eq!(ref_matcher.none_count, 1);
    assert_eq!(ref_matcher.values, vec![42]);
    println!("✓ Reference patterns in match work");

    // Test 10: State machine
    let mut conn = Connection {
        state: ConnectionState::Disconnected,
        retry_count: 0,
        success_count: 0,
        error_count: 0,
        messages: vec![],
    };
    conn.handle_event("connect");
    assert!(matches!(conn.state, ConnectionState::Connecting));
    conn.handle_event("success");
    assert!(matches!(conn.state, ConnectionState::Connected));
    assert_eq!(conn.success_count, 1);
    println!("✓ State machine pattern with view types works");

    println!("\n🎉 All match expression tests passed!");
    println!("   Match expressions work correctly with view-typed methods");
    println!("   Supports: basic match, destructuring, guards, nested, state machines");
}
