//@ check-pass
#![feature(view_types)]
#![allow(unused, incomplete_features)]

// TEST: Simple Tuple Struct Fields with View Types
//
// PURPOSE: Validate that numeric field syntax works in view specs

// =============================================================================
// Test 1: Basic Newtype Pattern
// =============================================================================

struct Counter(u32);

impl Counter {
    fn increment(&{mut 0} mut self) {
        self.0 += 1;
    }

    fn get(&{0} self) -> u32 {
        self.0
    }
}

// =============================================================================
// Test 2: Two-Field Tuple
// =============================================================================

struct Point(f32, f32);

impl Point {
    fn set_x(&{mut 0} mut self, x: f32) {
        self.0 = x;
    }

    fn set_y(&{mut 1} mut self, y: f32) {
        self.1 = y;
    }

    fn move_both(&{mut 0, mut 1} mut self, dx: f32, dy: f32) {
        self.0 += dx;
        self.1 += dy;
    }
}

// =============================================================================
// Test 3: Three Fields with Mixed Mutability
// =============================================================================

struct Triple(i32, i32, i32);

impl Triple {
    fn update_first(&{mut 0} mut self, v: i32) {
        self.0 = v;
    }

    fn read_second(&{1} self) -> i32 {
        self.1
    }

    fn mixed(&{mut 0, 1} mut self) {
        self.0 = self.1 * 2;
    }
}

// =============================================================================
// Test 4: Disjoint Field Borrowing
// =============================================================================

struct Data(u32, u32, u32);

impl Data {
    fn inc_0(&{mut 0} mut self) {
        self.0 += 1;
    }

    fn inc_1(&{mut 1} mut self) {
        self.1 += 1;
    }

    fn process(&mut self) {
        // Can call both because they access different fields
        self.inc_0();
        self.inc_1();
    }
}

// =============================================================================
// Main Test
// =============================================================================

fn main() {
    // Test 1: Newtype
    let mut counter = Counter(0);
    counter.increment();
    assert_eq!(counter.get(), 1);
    println!("✓ Newtype pattern works");

    // Test 2: Point
    let mut point = Point(0.0, 0.0);
    point.set_x(10.0);
    point.set_y(20.0);
    assert_eq!(point.0, 10.0);
    assert_eq!(point.1, 20.0);
    point.move_both(5.0, 5.0);
    assert_eq!(point.0, 15.0);
    assert_eq!(point.1, 25.0);
    println!("✓ Two-field tuple works");

    // Test 3: Mixed mutability
    let mut triple = Triple(10, 20, 30);
    triple.mixed();
    assert_eq!(triple.0, 40); // 20 * 2
    println!("✓ Mixed mutability works");

    // Test 4: Disjoint borrowing
    let mut data = Data(0, 0, 0);
    data.process();
    assert_eq!(data.0, 1);
    assert_eq!(data.1, 1);
    println!("✓ Disjoint field borrowing works");

    println!("\n🎉 All tuple field tests passed!");
}
