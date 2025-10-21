//@ check-pass
#![feature(view_types)]
#![allow(unused, incomplete_features)]

// TEST: Closures with View Types - Valid Patterns
//
// PURPOSE: Verify patterns where closures and view-typed methods work together.
//
// RATIONALE:
// Rust closures capture their entire environment, which limits some patterns.
// This test focuses on patterns that DO work:
// 1. Calling view-typed methods from within closures (iterator chains)
// 2. View-typed methods that take closures as parameters
// 3. Sequential use (closure finishes, then view-typed method)
//
// LIMITATIONS (tested in separate file):
// - Cannot define closure capturing self, then call view-typed method
// - Closures capture entire self, not individual fields

// =============================================================================
// Test 1: View-Typed Methods Called From Within Iterator Closures
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

    // Iterator closure calls view-typed method
    fn process_items(&mut self, items: Vec<String>) {
        items.into_iter().for_each(|item| {
            // Call view-typed method from within closure - WORKS!
            self.increment();
            self.add_data(item);
        });
    }
}

// =============================================================================
// Test 2: Iterator Chains with View-Typed Methods
// =============================================================================

struct Processor {
    total: i32,
    count: i32,
    errors: i32,
}

impl Processor {
    fn add_to_total(&{mut total} mut self, value: i32) {
        self.total += value;
    }

    fn increment_count(&{mut count} mut self) {
        self.count += 1;
    }

    fn increment_errors(&{mut errors} mut self) {
        self.errors += 1;
    }

    // Complex iterator chain with multiple view-typed method calls
    fn process_values(&mut self, values: Vec<i32>) {
        values.iter()
            .filter(|&&v| v > 0)
            .for_each(|&v| {
                self.add_to_total(v);
                self.increment_count();
            });
    }

    // Map with view-typed methods
    fn transform_and_process(&mut self, values: Vec<i32>) -> Vec<i32> {
        values.iter().map(|&v| {
            if v < 0 {
                self.increment_errors();
                0
            } else {
                self.increment_count();
                v * 2
            }
        }).collect()
    }
}

// =============================================================================
// Test 3: View-Typed Methods That Accept Closures
// =============================================================================

struct Config {
    retry_count: u32,
    timeout: u32,
}

impl Config {
    fn increment_retries(&{mut retry_count} mut self) {
        self.retry_count += 1;
    }

    fn set_timeout(&{mut timeout} mut self, value: u32) {
        self.timeout = value;
    }

    // View-typed method that accepts a closure parameter
    fn retry_with_callback<F>(&{mut retry_count, timeout} mut self, mut callback: F) -> bool
    where
        F: FnMut(u32) -> bool,
    {
        while self.retry_count < 3 {
            self.increment_retries();
            if callback(self.timeout) {
                return true;
            }
        }
        false
    }

    fn test_retry(&mut self) {
        let mut attempts = 0;
        self.retry_with_callback(|_timeout| {
            attempts += 1;
            attempts >= 2
        });
    }
}

// =============================================================================
// Test 4: Sequential Pattern - Closure First, Then View Method
// =============================================================================

struct Sequential {
    x: i32,
    y: i32,
}

impl Sequential {
    fn update_x(&{mut x} mut self, value: i32) {
        self.x = value;
    }

    fn update_y(&{mut y} mut self, value: i32) {
        self.y = value;
    }

    // Closure completes, then view-typed methods called
    fn sequential_updates(&mut self) {
        // Closure scope
        {
            let values = vec![1, 2, 3];
            let _sum: i32 = values.iter().sum();
            // Closure doesn't capture self at all
        }

        // After closure is done, call view-typed methods
        self.update_x(10);
        self.update_y(20);
    }
}

// =============================================================================
// Test 5: Real-World ECS Pattern
// =============================================================================

struct Entity {
    position: (f32, f32, f32),
    velocity: (f32, f32, f32),
    health: f32,
}

impl Entity {
    fn update_position(&{mut position, velocity} mut self, dt: f32) {
        self.position.0 += self.velocity.0 * dt;
        self.position.1 += self.velocity.1 * dt;
        self.position.2 += self.velocity.2 * dt;
    }

    fn take_damage(&{mut health} mut self, damage: f32) {
        self.health -= damage;
    }

    // Game loop pattern: iterator with view-typed methods
    fn update_with_events(&mut self, dt: f32, events: Vec<&str>) {
        // Physics first
        self.update_position(dt);

        // Then process events in closure
        events.iter().for_each(|&event| {
            match event {
                "damage" => self.take_damage(10.0),
                _ => {}
            }
        });
    }
}

// =============================================================================
// Test 6: Closure as Return Value from View-Typed Method
// =============================================================================

struct Factory {
    multiplier: i32,
}

impl Factory {
    // View-typed method that returns a closure
    fn get_multiplier_fn(&{multiplier} self) -> impl Fn(i32) -> i32 {
        let m = self.multiplier;
        move |x| x * m
    }

    fn test_factory(&self) {
        let f = self.get_multiplier_fn();
        let result = f(5);
        assert_eq!(result, 5 * self.multiplier);
    }
}

// =============================================================================
// Test 7: Multiple View-Typed Methods in Iterator Chain
// =============================================================================

struct Statistics {
    min: i32,
    max: i32,
    sum: i32,
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

    fn add_to_sum(&{mut sum} mut self, value: i32) {
        self.sum += value;
    }

    fn increment_count(&{mut count} mut self) {
        self.count += 1;
    }

    // Process values calling multiple view-typed methods
    fn analyze(&mut self, values: Vec<i32>) {
        values.iter().for_each(|&v| {
            self.update_min(v);
            self.update_max(v);
            self.add_to_sum(v);
            self.increment_count();
        });
    }
}

// =============================================================================
// Test 8: Try/Catch Pattern with Closures
// =============================================================================

struct ErrorHandler {
    error_count: u32,
    success_count: u32,
}

impl ErrorHandler {
    fn increment_errors(&{mut error_count} mut self) {
        self.error_count += 1;
    }

    fn increment_success(&{mut success_count} mut self) {
        self.success_count += 1;
    }

    fn process_with_error_handling(&mut self, operations: Vec<Result<i32, String>>) {
        operations.iter().for_each(|op| {
            match op {
                Ok(_) => self.increment_success(),
                Err(_) => self.increment_errors(),
            }
        });
    }
}

// =============================================================================
// Test 9: Conditional Execution in Closures
// =============================================================================

struct Conditional {
    a: i32,
    b: i32,
    c: i32,
}

impl Conditional {
    fn update_a(&{mut a} mut self, v: i32) {
        self.a = v;
    }

    fn update_b(&{mut b} mut self, v: i32) {
        self.b = v;
    }

    fn update_c(&{mut c} mut self, v: i32) {
        self.c = v;
    }

    // Conditional logic in closure calling different view-typed methods
    fn conditional_updates(&mut self, values: Vec<i32>) {
        values.iter().enumerate().for_each(|(i, &v)| {
            match i % 3 {
                0 => self.update_a(v),
                1 => self.update_b(v),
                2 => self.update_c(v),
                _ => unreachable!(),
            }
        });
    }
}

// =============================================================================
// Main Test Driver
// =============================================================================

fn main() {
    // Test 1: Iterator closures
    let mut counter = Counter {
        count: 0,
        data: vec![],
    };
    counter.process_items(vec!["a".to_string(), "b".to_string()]);
    assert_eq!(counter.count, 2);
    assert_eq!(counter.data.len(), 2);
    println!("✓ Iterator closures with view types work");

    // Test 2: Iterator chains
    let mut proc = Processor {
        total: 0,
        count: 0,
        errors: 0,
    };
    proc.process_values(vec![1, -1, 2, -2, 3]);
    assert_eq!(proc.count, 3); // Only positive values
    assert_eq!(proc.total, 6); // 1 + 2 + 3

    let mut proc2 = Processor {
        total: 0,
        count: 0,
        errors: 0,
    };
    let result = proc2.transform_and_process(vec![1, -1, 2]);
    assert_eq!(result, vec![2, 0, 4]);
    assert_eq!(proc2.count, 2);
    assert_eq!(proc2.errors, 1);
    println!("✓ Iterator chains with view types work");

    // Test 3: Closures as parameters
    let mut config = Config {
        retry_count: 0,
        timeout: 1000,
    };
    config.test_retry();
    println!("✓ Closures as parameters work");

    // Test 4: Sequential pattern
    let mut seq = Sequential { x: 0, y: 0 };
    seq.sequential_updates();
    assert_eq!(seq.x, 10);
    assert_eq!(seq.y, 20);
    println!("✓ Sequential pattern works");

    // Test 5: ECS pattern
    let mut entity = Entity {
        position: (0.0, 0.0, 0.0),
        velocity: (1.0, 0.0, 0.0),
        health: 100.0,
    };
    entity.update_with_events(1.0, vec!["damage", "damage"]);
    assert_eq!(entity.position.0, 1.0);
    assert_eq!(entity.health, 80.0);
    println!("✓ ECS pattern works");

    // Test 6: Closure return value
    let factory = Factory { multiplier: 3 };
    factory.test_factory();
    println!("✓ Closure return values work");

    // Test 7: Statistics
    let mut stats = Statistics {
        min: i32::MAX,
        max: i32::MIN,
        sum: 0,
        count: 0,
    };
    stats.analyze(vec![5, 2, 8, 1, 9]);
    assert_eq!(stats.min, 1);
    assert_eq!(stats.max, 9);
    assert_eq!(stats.sum, 25);
    assert_eq!(stats.count, 5);
    println!("✓ Statistics pattern works");

    // Test 8: Error handling
    let mut handler = ErrorHandler {
        error_count: 0,
        success_count: 0,
    };
    handler.process_with_error_handling(vec![
        Ok(1),
        Err("error".to_string()),
        Ok(2),
    ]);
    assert_eq!(handler.success_count, 2);
    assert_eq!(handler.error_count, 1);
    println!("✓ Error handling pattern works");

    // Test 9: Conditional updates
    let mut cond = Conditional { a: 0, b: 0, c: 0 };
    cond.conditional_updates(vec![10, 20, 30, 40, 50, 60]);
    assert_eq!(cond.a, 40); // indices 0, 3
    assert_eq!(cond.b, 50); // indices 1, 4
    assert_eq!(cond.c, 60); // indices 2, 5
    println!("✓ Conditional updates work");

    println!("\n🎉 All closure tests passed!");
    println!("   View-typed methods work correctly within iterator closures");
    println!("   This is the recommended pattern for using closures with view types");
}
