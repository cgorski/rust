//@ check-pass
#![feature(view_types)]
#![allow(unused, incomplete_features)]

// TEST: Field Shadowing by Local Variables
//
// PURPOSE: Verify that local variables with the same name as struct fields
// don't interfere with view type field access validation.
//
// RATIONALE:
// In Rust, local variables can shadow struct field names. For example:
//   let x = 10;  // local variable
//   self.x = 5;  // field access
//
// With view types, we need to ensure that:
// 1. Local variable shadowing doesn't prevent field access
// 2. View type validation correctly distinguishes self.field from local variable
// 3. The local variable gets its own binding, field remains accessible via self
//
// This is a scoping issue, not a view types issue, but we need to verify
// the interaction works correctly.

// =============================================================================
// Test 1: Basic Field Shadowing - Single Field
// =============================================================================

struct Counter {
    count: u32,
    max: u32,
}

impl Counter {
    // Local variable 'count' shadows field name
    fn increment_shadowed(&{mut count} mut self) {
        let count = 100; // Local variable shadows field name

        // Field access still works via self
        self.count += 1;

        // Local variable is independent
        let _local = count; // Uses local variable (100)
        assert_eq!(_local, 100);
    }

    // Verify field was actually modified
    fn get_count(&{count} self) -> u32 {
        self.count
    }
}

// =============================================================================
// Test 2: Multiple Field Shadowing
// =============================================================================

struct Point {
    x: f32,
    y: f32,
    z: f32,
}

impl Point {
    // Shadow all three fields with local variables
    fn update_all_shadowed(&{mut x, mut y, mut z} mut self, dx: f32, dy: f32, dz: f32) {
        // Shadow all field names
        let x = 1.0;
        let y = 2.0;
        let z = 3.0;

        // Field access still works
        self.x += dx;
        self.y += dy;
        self.z += dz;

        // Local variables are independent
        let _sum = x + y + z; // Uses locals (6.0)
    }

    // Shadow some fields, not others
    fn update_xy_shadowed(&{mut x, mut y, z} mut self) {
        let x = 999.0; // Shadow x
        let y = 888.0; // Shadow y
        // Don't shadow z

        // Field access via self
        self.x = self.z * 2.0; // Can read z, write x
        self.y = self.z * 3.0; // Can read z, write y

        // Locals are different
        assert_eq!(x, 999.0);
        assert_eq!(y, 888.0);
    }
}

// =============================================================================
// Test 3: Nested Scope Shadowing
// =============================================================================

struct Data {
    value: i32,
    multiplier: i32,
}

impl Data {
    fn nested_shadowing(&{mut value, multiplier} mut self) {
        let value = 10; // Shadow at outer scope

        {
            let value = 20; // Shadow at inner scope

            // Field access still works
            self.value = self.multiplier * 5;

            // Inner local
            assert_eq!(value, 20);
        }

        // Outer local
        assert_eq!(value, 10);

        // Field was modified
        // (can't assert here without another read, but test validates it compiles)
    }
}

// =============================================================================
// Test 4: Shadowing with Same Type
// =============================================================================

struct Config {
    setting: String,
    backup: String,
}

impl Config {
    fn update_with_shadow(&{mut setting} mut self, new_value: String) {
        // Local variable with same name AND same type as field
        let setting = String::from("temporary");

        // Use local variable
        println!("Local: {}", setting);

        // Field access via self
        self.setting = new_value;

        // Local is still "temporary"
        assert_eq!(setting, "temporary");
    }
}

// =============================================================================
// Test 5: Shadowing in Loops
// =============================================================================

struct Accumulator {
    sum: i32,
    count: i32,
}

impl Accumulator {
    fn accumulate(&{mut sum, mut count} mut self, values: &[i32]) {
        for sum in values.iter() {  // 'sum' shadows field name in loop variable
            // Field access
            self.sum += sum;  // Field += loop variable
            self.count += 1;
        }
    }

    fn accumulate_index(&{mut sum} mut self, values: &[i32]) {
        for sum in 0..values.len() {  // 'sum' is loop counter, shadows field
            // Field access
            self.sum += values[sum]; // Field += values[loop counter]
        }
    }
}

// =============================================================================
// Test 6: Shadowing with Match Patterns
// =============================================================================

struct Matcher {
    x: i32,
    y: i32,
}

impl Matcher {
    fn match_shadow(&{mut x, mut y} mut self, option: Option<i32>) {
        match option {
            Some(x) => {  // 'x' in pattern shadows field
                // Field access
                self.x = x * 2;  // Field = pattern variable * 2
                self.y = x + 1;  // Field = pattern variable + 1
            }
            None => {
                self.x = 0;
                self.y = 0;
            }
        }
    }
}

// =============================================================================
// Test 7: Complex Real-World Scenario
// =============================================================================

struct GameEntity {
    position: f32,
    velocity: f32,
    health: f32,
}

impl GameEntity {
    fn update_physics(&{mut position, mut velocity, health} mut self, dt: f32) {
        // Calculate new values with shadowed local variables
        let position = self.position + self.velocity * dt;  // Shadow field
        let velocity = self.velocity * 0.99;  // Apply drag, shadow field

        // Conditional logic using locals
        if position < 0.0 {
            // Write to fields
            self.position = 0.0;
            self.velocity = 0.0;
        } else {
            // Write locals to fields
            self.position = position;
            self.velocity = velocity;
        }

        // Read field that wasn't shadowed
        if self.health < 10.0 {
            self.velocity *= 0.5; // Slow down when low health
        }
    }
}

// =============================================================================
// Test 8: Shadowing in Closures
// =============================================================================

struct Processor {
    total: i32,
    count: i32,
}

impl Processor {
    fn process_with_closure(&{mut total, mut count} mut self, values: Vec<i32>) {
        let total = 999; // Shadow field with local

        // Closure captures local 'total'
        let _closure = || {
            println!("Captured local total: {}", total); // Uses local (999)
        };

        // But we can still access field
        values.into_iter().for_each(|v| {
            self.total += v;  // Field access
            self.count += 1;  // Field access
        });

        _closure(); // Uses captured local
    }
}

// =============================================================================
// Test 9: Immutable Field Access with Shadowing
// =============================================================================

struct ReadOnly {
    value: i32,
    name: String,
}

impl ReadOnly {
    fn read_with_shadow(&{value, name} self) -> i32 {
        let value = 42; // Shadow field
        let name = String::from("local"); // Shadow field

        // Can still read fields
        let field_value = self.value;
        let field_name = &self.name;

        // Locals are independent
        assert_eq!(value, 42);
        assert_eq!(name, "local");

        field_value // Return field, not local
    }
}

// =============================================================================
// Test 10: Mutable Reference Shadowing
// =============================================================================

struct RefTest {
    data: Vec<i32>,
}

impl RefTest {
    fn shadow_mut_ref(&{mut data} mut self) {
        // Local mutable reference with same name
        let mut data = vec![1, 2, 3];

        // Modify local
        data.push(4);
        assert_eq!(data.len(), 4);

        // Modify field
        self.data.push(100);

        // They're independent
        assert_eq!(data[0], 1);    // Local
        // (Field assertion would need another method)
    }
}

// =============================================================================
// Main Test Driver
// =============================================================================

fn main() {
    // Test 1: Basic shadowing
    let mut counter = Counter { count: 0, max: 100 };
    counter.increment_shadowed();
    assert_eq!(counter.get_count(), 1);
    println!("✓ Basic field shadowing works");

    // Test 2: Multiple field shadowing
    let mut point = Point { x: 0.0, y: 0.0, z: 1.0 };
    point.update_all_shadowed(1.0, 2.0, 3.0);
    assert_eq!(point.x, 1.0);
    point.update_xy_shadowed();
    assert_eq!(point.x, 2.0); // z was 1.0, x = z * 2
    println!("✓ Multiple field shadowing works");

    // Test 3: Nested scope shadowing
    let mut data = Data { value: 0, multiplier: 3 };
    data.nested_shadowing();
    assert_eq!(data.value, 15); // multiplier * 5
    println!("✓ Nested scope shadowing works");

    // Test 4: Same type shadowing
    let mut config = Config {
        setting: String::from("old"),
        backup: String::from("backup"),
    };
    config.update_with_shadow(String::from("new"));
    assert_eq!(config.setting, "new");
    println!("✓ Same type shadowing works");

    // Test 5: Loop shadowing
    let mut acc = Accumulator { sum: 0, count: 0 };
    acc.accumulate(&[1, 2, 3]);
    assert_eq!(acc.sum, 6);
    assert_eq!(acc.count, 3);

    let mut acc2 = Accumulator { sum: 0, count: 0 };
    acc2.accumulate_index(&[10, 20, 30]);
    assert_eq!(acc2.sum, 60);
    println!("✓ Loop shadowing works");

    // Test 6: Match pattern shadowing
    let mut matcher = Matcher { x: 0, y: 0 };
    matcher.match_shadow(Some(5));
    assert_eq!(matcher.x, 10); // 5 * 2
    assert_eq!(matcher.y, 6);  // 5 + 1
    println!("✓ Match pattern shadowing works");

    // Test 7: Complex scenario
    let mut entity = GameEntity {
        position: 10.0,
        velocity: 2.0,
        health: 100.0,
    };
    entity.update_physics(1.0);
    println!("✓ Complex shadowing scenario works");

    // Test 8: Closure shadowing
    let mut proc = Processor { total: 0, count: 0 };
    proc.process_with_closure(vec![1, 2, 3]);
    assert_eq!(proc.total, 6);
    assert_eq!(proc.count, 3);
    println!("✓ Closure shadowing works");

    // Test 9: Immutable shadowing
    let readonly = ReadOnly {
        value: 123,
        name: String::from("field"),
    };
    let result = readonly.read_with_shadow();
    assert_eq!(result, 123); // Returns field, not local
    println!("✓ Immutable shadowing works");

    // Test 10: Mutable reference shadowing
    let mut ref_test = RefTest { data: vec![] };
    ref_test.shadow_mut_ref();
    assert_eq!(ref_test.data.len(), 1); // Field has one element
    println!("✓ Mutable reference shadowing works");

    println!("\n🎉 All field shadowing tests passed!");
    println!("   View types correctly handle local variable shadowing");
}
