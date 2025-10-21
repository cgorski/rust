//@ check-pass
#![feature(view_types)]
#![allow(unused, incomplete_features)]

// SANITY CHECK: Basic Conflict Detection
//
// This is a minimal test to verify that the most fundamental cases work:
// 1. Disjoint fields CAN be borrowed simultaneously
// 2. View-typed methods CAN be called when their views don't conflict
// 3. The motivating example from the paper actually compiles

// =============================================================================
// Test 1: The Absolute Basics - Two Disjoint Fields
// =============================================================================

struct TwoFields {
    field_a: i32,
    field_b: String,
}

impl TwoFields {
    fn mutate_a(&{mut field_a} mut self) {
        self.field_a = 42;
    }

    fn mutate_b(&{mut field_b} mut self) {
        self.field_b = String::from("hello");
    }

    // MUST WORK: field_a and field_b are completely disjoint
    fn test_basic_disjoint(&mut self) {
        let _borrow_b = &mut self.field_b;  // Borrow field_b
        self.mutate_a();                     // Use field_a via view type
                                             // This MUST compile!
    }
}

// =============================================================================
// Test 2: The Motivating Example (from SPLASH 2025 paper)
// =============================================================================

struct Item {
    id: usize,
    data: String,
}

struct S {
    next_id: usize,
    data: Vec<Item>,
}

impl S {
    fn new_id(&{mut next_id} mut self) -> usize {
        let i = self.next_id;
        self.next_id += 1;
        i
    }

    // This is THE example from the paper - it MUST work!
    fn assign_ids(&mut self) {
        for item in &mut self.data {
            let id = self.new_id();  // ✓ View type makes this legal
            item.id = id;
        }
    }
}

// =============================================================================
// Test 3: Three Disjoint Fields
// =============================================================================

struct ThreeFields {
    x: i32,
    y: i32,
    z: i32,
}

impl ThreeFields {
    fn inc_x(&{mut x} mut self) {
        self.x += 1;
    }

    fn inc_y(&{mut y} mut self) {
        self.y += 1;
    }

    fn inc_z(&{mut z} mut self) {
        self.z += 1;
    }

    fn test_all_three_disjoint(&mut self) {
        let _borrow_x = &mut self.x;
        self.inc_y();  // Different field
        self.inc_z();  // Different field
    }
}

// =============================================================================
// Test 4: Immutable Views Don't Conflict with Each Other
// =============================================================================

struct ReadOnly {
    data_a: Vec<i32>,
    data_b: Vec<i32>,
}

impl ReadOnly {
    fn sum_a(&{data_a} self) -> i32 {
        self.data_a.iter().sum()
    }

    fn sum_b(&{data_b} self) -> i32 {
        self.data_b.iter().sum()
    }

    fn both_sums(&self) -> (i32, i32) {
        let _borrow_a = &self.data_a;  // Immutable borrow
        let sum_b = self.sum_b();       // Immutable view of different field
        let sum_a = self.sum_a();       // Immutable view works with borrow
        (sum_a, sum_b)
    }
}

// =============================================================================
// Test 5: Nested Disjoint Paths
// =============================================================================

struct Vec3 {
    x: f32,
    y: f32,
    z: f32,
}

struct Transform {
    position: Vec3,
    rotation: Vec3,
}

struct Entity {
    transform: Transform,
    health: f32,
}

impl Entity {
    fn update_position(&{mut transform.position} mut self) {
        self.transform.position.x = 1.0;
    }

    fn update_rotation(&{mut transform.rotation} mut self) {
        self.transform.rotation.x = 0.5;
    }

    // MUST WORK: position and rotation are disjoint nested paths
    fn test_nested_disjoint(&mut self) {
        let _pos = &mut self.transform.position;
        self.update_rotation();  // Uses different nested path
    }
}

// =============================================================================
// Test 6: View Composition - View Calls View
// =============================================================================

struct Composed {
    a: i32,
    b: i32,
}

impl Composed {
    fn uses_a(&{mut a} mut self) {
        self.a += 1;
    }

    fn also_uses_a(&{mut a} mut self) {
        self.uses_a();  // View calls another view with same field
    }

    fn uses_b(&{mut b} mut self) {
        self.b += 1;
    }

    fn mixed(&{mut a} mut self) {
        self.uses_b();  // View {a} calls view {b} - disjoint!
    }
}

// =============================================================================
// Main: Execute all sanity checks
// =============================================================================

fn main() {
    let mut tf = TwoFields {
        field_a: 0,
        field_b: String::new(),
    };
    tf.test_basic_disjoint();

    let mut s = S {
        next_id: 1,
        data: vec![
            Item { id: 0, data: String::from("first") },
            Item { id: 0, data: String::from("second") },
        ],
    };
    s.assign_ids();
    assert_eq!(s.next_id, 3);
    assert_eq!(s.data[0].id, 1);
    assert_eq!(s.data[1].id, 2);

    let mut three = ThreeFields { x: 0, y: 0, z: 0 };
    three.test_all_three_disjoint();

    let ro = ReadOnly {
        data_a: vec![1, 2, 3],
        data_b: vec![4, 5, 6],
    };
    let (sum_a, sum_b) = ro.both_sums();
    assert_eq!(sum_a, 6);
    assert_eq!(sum_b, 15);

    let mut entity = Entity {
        transform: Transform {
            position: Vec3 { x: 0.0, y: 0.0, z: 0.0 },
            rotation: Vec3 { x: 0.0, y: 0.0, z: 0.0 },
        },
        health: 100.0,
    };
    entity.test_nested_disjoint();

    let mut comp = Composed { a: 0, b: 0 };
    comp.also_uses_a();
    comp.mixed();

    println!("✓ All sanity checks passed!");
}
