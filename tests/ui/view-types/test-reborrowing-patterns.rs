//@ check-pass
#![feature(view_types)]
#![allow(unused, incomplete_features)]

// TEST: Reborrowing Patterns with View Types
//
// PURPOSE: Verify that reborrowing (&mut *x) works correctly with view-typed methods.
// Test various reborrowing scenarios including helper functions, multiple reborrows,
// and real-world patterns.
//
// RATIONALE:
// Reborrowing is a common Rust pattern where a mutable reference is temporarily
// "reborrowed" to create a new, shorter-lived mutable reference. This is essential for:
// - Passing mutable references to helper functions
// - Creating temporary scoped references
// - Working around borrow checker limitations
//
// With view types, we need to ensure that:
// 1. Reborrows work with view-typed method calls
// 2. View-typed methods can be called on reborrowed references
// 3. Multiple reborrows in sequence work correctly
// 4. Reborrowing doesn't interfere with view type semantics

// =============================================================================
// Test 1: Basic Reborrowing with View-Typed Methods
// =============================================================================

struct Counter {
    count: u32,
    data: Vec<String>,
}

impl Counter {
    fn increment(&{mut count} mut self) {
        self.count += 1;
    }

    fn add_data(&{mut data} mut self, item: String) {
        self.data.push(item);
    }

    fn get_count(&{count} self) -> u32 {
        self.count
    }
}

// Helper function that takes a mutable reference
fn increment_helper(counter: &mut Counter) {
    counter.increment(); // View-typed method call through reference
}

// Helper function with reborrow in body
fn process_counter(counter: &mut Counter) {
    let reborrow = &mut *counter;
    reborrow.increment();
}

// =============================================================================
// Test 2: Reborrowing in Nested Function Calls
// =============================================================================

struct Point {
    x: f32,
    y: f32,
    z: f32,
}

impl Point {
    fn set_x(&{mut x} mut self, value: f32) {
        self.x = value;
    }

    fn set_y(&{mut y} mut self, value: f32) {
        self.y = value;
    }

    fn set_z(&{mut z} mut self, value: f32) {
        self.z = value;
    }
}

fn set_x_helper(point: &mut Point, value: f32) {
    point.set_x(value);
}

fn set_y_helper(point: &mut Point, value: f32) {
    point.set_y(value);
}

fn set_all(point: &mut Point, x: f32, y: f32, z: f32) {
    set_x_helper(&mut *point, x); // Explicit reborrow
    set_y_helper(&mut *point, y); // Another reborrow
    point.set_z(z);                // Direct call
}

// =============================================================================
// Test 3: Multiple Sequential Reborrows
// =============================================================================

struct Data {
    a: i32,
    b: i32,
    c: i32,
}

impl Data {
    fn update_a(&{mut a} mut self, value: i32) {
        self.a = value;
    }

    fn update_b(&{mut b} mut self, value: i32) {
        self.b = value;
    }

    fn update_c(&{mut c} mut self, value: i32) {
        self.c = value;
    }
}

fn update_through_reborrows(data: &mut Data) {
    // Multiple sequential reborrows
    {
        let reborrow1 = &mut *data;
        reborrow1.update_a(1);
    }
    {
        let reborrow2 = &mut *data;
        reborrow2.update_b(2);
    }
    {
        let reborrow3 = &mut *data;
        reborrow3.update_c(3);
    }
}

// =============================================================================
// Test 4: Reborrowing in Conditionals
// =============================================================================

struct Config {
    enabled: bool,
    timeout: u32,
    retries: u32,
}

impl Config {
    fn set_timeout(&{mut timeout} mut self, value: u32) {
        self.timeout = value;
    }

    fn set_retries(&{mut retries} mut self, value: u32) {
        self.retries = value;
    }

    fn enable(&{mut enabled} mut self) {
        self.enabled = true;
    }

    fn disable(&{mut enabled} mut self) {
        self.enabled = false;
    }
}

fn configure_conditionally(config: &mut Config, enable: bool) {
    if enable {
        let reborrow = &mut *config;
        reborrow.enable();
        reborrow.set_timeout(5000);
    } else {
        let reborrow = &mut *config;
        reborrow.disable();
        reborrow.set_retries(3);
    }
}

// =============================================================================
// Test 5: Reborrowing in Loops
// =============================================================================

struct Accumulator {
    sum: i32,
    count: i32,
}

impl Accumulator {
    fn add(&{mut sum} mut self, value: i32) {
        self.sum += value;
    }

    fn increment_count(&{mut count} mut self) {
        self.count += 1;
    }
}

fn accumulate_with_reborrows(acc: &mut Accumulator, values: &[i32]) {
    for &value in values {
        let reborrow = &mut *acc;
        reborrow.add(value);
        reborrow.increment_count();
    }
}

// =============================================================================
// Test 6: Reborrowing with Immutable and Mutable References
// =============================================================================

struct Statistics {
    min: i32,
    max: i32,
    count: i32,
}

impl Statistics {
    fn update_min(&{mut min} mut self, value: i32) {
        if value < self.min {
            self.min = value;
        }
    }

    fn update_max(&{mut max} mut self, value: i32) {
        if value > self.max {
            self.max = value;
        }
    }

    fn increment_count(&{mut count} mut self) {
        self.count += 1;
    }

    fn get_min(&{min} self) -> i32 {
        self.min
    }
}

fn process_value(stats: &mut Statistics, value: i32) {
    // Reborrow for mutation
    {
        let reborrow = &mut *stats;
        reborrow.update_min(value);
        reborrow.update_max(value);
        reborrow.increment_count();
    }

    // Immutable borrow after reborrow scope ends
    let _min = stats.get_min();
}

// =============================================================================
// Test 7: Reborrowing in Match Arms
// =============================================================================

enum Command {
    Add(i32),
    Subtract(i32),
    Reset,
}

struct Calculator {
    result: i32,
    operation_count: i32,
}

impl Calculator {
    fn add(&{mut result} mut self, value: i32) {
        self.result += value;
    }

    fn subtract(&{mut result} mut self, value: i32) {
        self.result -= value;
    }

    fn reset(&{mut result, mut operation_count} mut self) {
        self.result = 0;
        self.operation_count = 0;
    }

    fn increment_ops(&{mut operation_count} mut self) {
        self.operation_count += 1;
    }
}

fn execute_command(calc: &mut Calculator, cmd: Command) {
    match cmd {
        Command::Add(value) => {
            let reborrow = &mut *calc;
            reborrow.add(value);
            reborrow.increment_ops();
        }
        Command::Subtract(value) => {
            let reborrow = &mut *calc;
            reborrow.subtract(value);
            reborrow.increment_ops();
        }
        Command::Reset => {
            calc.reset();
        }
    }
}

// =============================================================================
// Test 8: Reborrowing Through Multiple Helper Layers
// =============================================================================

struct Entity {
    position: f32,
    velocity: f32,
    health: f32,
}

impl Entity {
    fn set_position(&{mut position} mut self, value: f32) {
        self.position = value;
    }

    fn set_velocity(&{mut velocity} mut self, value: f32) {
        self.velocity = value;
    }

    fn take_damage(&{mut health} mut self, damage: f32) {
        self.health -= damage;
    }
}

fn level3_helper(entity: &mut Entity) {
    entity.set_position(100.0);
}

fn level2_helper(entity: &mut Entity) {
    level3_helper(&mut *entity); // Reborrow through layers
    entity.set_velocity(50.0);
}

fn level1_helper(entity: &mut Entity) {
    level2_helper(&mut *entity); // Another reborrow
    entity.take_damage(10.0);
}

// =============================================================================
// Test 9: Reborrowing with Closures
// =============================================================================

struct Processor {
    total: i32,
    count: i32,
}

impl Processor {
    fn add_to_total(&{mut total} mut self, value: i32) {
        self.total += value;
    }

    fn increment_count(&{mut count} mut self) {
        self.count += 1;
    }
}

fn process_with_closure(proc: &mut Processor, values: Vec<i32>) {
    values.into_iter().for_each(|v| {
        // Closure calls view-typed methods
        proc.add_to_total(v);
        proc.increment_count();
    });
}

// =============================================================================
// Test 10: Real-World Pattern - Option/Result Chaining
// =============================================================================

struct Connection {
    connection_count: u32,
    error_count: u32,
    retry_count: u32,
}

impl Connection {
    fn increment_connections(&{mut connection_count} mut self) {
        self.connection_count += 1;
    }

    fn increment_errors(&{mut error_count} mut self) {
        self.error_count += 1;
    }

    fn increment_retries(&{mut retry_count} mut self) {
        self.retry_count += 1;
    }
}

fn attempt_connection(conn: &mut Connection) -> Result<(), String> {
    let reborrow = &mut *conn;
    reborrow.increment_connections();

    if reborrow.connection_count % 2 == 0 {
        Ok(())
    } else {
        reborrow.increment_errors();
        Err("Connection failed".to_string())
    }
}

fn try_with_retries(conn: &mut Connection, max_retries: u32) -> Result<(), String> {
    for _ in 0..max_retries {
        match attempt_connection(&mut *conn) {
            Ok(()) => return Ok(()),
            Err(_) => {
                conn.increment_retries();
            }
        }
    }
    Err("Max retries exceeded".to_string())
}

// =============================================================================
// Test 11: Reborrowing in Generic Contexts
// =============================================================================

struct GenericContainer<T> {
    value: T,
    metadata: String,
}

impl<T> GenericContainer<T> {
    fn set_metadata(&{mut metadata} mut self, meta: String) {
        self.metadata = meta;
    }
}

fn update_metadata<T>(container: &mut GenericContainer<T>, meta: String) {
    let reborrow = &mut *container;
    reborrow.set_metadata(meta);
}

// =============================================================================
// Main Test Driver
// =============================================================================

fn main() {
    // Test 1: Basic reborrowing
    let mut counter = Counter {
        count: 0,
        data: vec![],
    };
    increment_helper(&mut counter);
    assert_eq!(counter.count, 1);
    process_counter(&mut counter);
    assert_eq!(counter.count, 2);
    println!("✓ Basic reborrowing works");

    // Test 2: Nested function calls
    let mut point = Point { x: 0.0, y: 0.0, z: 0.0 };
    set_all(&mut point, 1.0, 2.0, 3.0);
    assert_eq!(point.x, 1.0);
    assert_eq!(point.y, 2.0);
    assert_eq!(point.z, 3.0);
    println!("✓ Nested function calls with reborrows work");

    // Test 3: Multiple sequential reborrows
    let mut data = Data { a: 0, b: 0, c: 0 };
    update_through_reborrows(&mut data);
    assert_eq!(data.a, 1);
    assert_eq!(data.b, 2);
    assert_eq!(data.c, 3);
    println!("✓ Multiple sequential reborrows work");

    // Test 4: Conditionals
    let mut config = Config {
        enabled: false,
        timeout: 0,
        retries: 0,
    };
    configure_conditionally(&mut config, true);
    assert_eq!(config.enabled, true);
    assert_eq!(config.timeout, 5000);
    println!("✓ Reborrowing in conditionals works");

    // Test 5: Loops
    let mut acc = Accumulator { sum: 0, count: 0 };
    accumulate_with_reborrows(&mut acc, &[1, 2, 3, 4]);
    assert_eq!(acc.sum, 10);
    assert_eq!(acc.count, 4);
    println!("✓ Reborrowing in loops works");

    // Test 6: Mixed mutability
    let mut stats = Statistics {
        min: i32::MAX,
        max: i32::MIN,
        count: 0,
    };
    process_value(&mut stats, 42);
    assert_eq!(stats.min, 42);
    assert_eq!(stats.max, 42);
    assert_eq!(stats.count, 1);
    println!("✓ Reborrowing with mixed mutability works");

    // Test 7: Match arms
    let mut calc = Calculator {
        result: 0,
        operation_count: 0,
    };
    execute_command(&mut calc, Command::Add(10));
    assert_eq!(calc.result, 10);
    execute_command(&mut calc, Command::Subtract(3));
    assert_eq!(calc.result, 7);
    assert_eq!(calc.operation_count, 2);
    println!("✓ Reborrowing in match arms works");

    // Test 8: Multiple helper layers
    let mut entity = Entity {
        position: 0.0,
        velocity: 0.0,
        health: 100.0,
    };
    level1_helper(&mut entity);
    assert_eq!(entity.position, 100.0);
    assert_eq!(entity.velocity, 50.0);
    assert_eq!(entity.health, 90.0);
    println!("✓ Reborrowing through multiple layers works");

    // Test 9: Closures
    let mut proc = Processor { total: 0, count: 0 };
    process_with_closure(&mut proc, vec![5, 10, 15]);
    assert_eq!(proc.total, 30);
    assert_eq!(proc.count, 3);
    println!("✓ Reborrowing with closures works");

    // Test 10: Option/Result chaining
    let mut conn = Connection {
        connection_count: 0,
        error_count: 0,
        retry_count: 0,
    };
    let _ = try_with_retries(&mut conn, 3);
    assert!(conn.connection_count > 0);
    println!("✓ Reborrowing with Result chaining works");

    // Test 11: Generic contexts
    let mut container = GenericContainer {
        value: 42,
        metadata: String::from("initial"),
    };
    update_metadata(&mut container, String::from("updated"));
    assert_eq!(container.metadata, "updated");
    println!("✓ Reborrowing in generic contexts works");

    println!("\n🎉 All reborrowing tests passed!");
    println!("   Reborrowing works correctly with view-typed methods");
    println!("   Supports: helpers, loops, conditionals, match, closures, generics");
}
