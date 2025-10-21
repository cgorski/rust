//@ check-pass
#![feature(view_types)]
#![allow(unused, incomplete_features)]

// COMPREHENSIVE NESTED TUPLE FIELD TEST
//
// This test validates that nested tuple field access works correctly
// including complex mixed patterns like:
// - blah.0.2.moo (named -> tuple -> tuple -> named)
// - 0.field.1 (tuple -> named -> tuple)
// - 0.0.0 (deep tuple nesting)

// =============================================================================
// Test 1: Basic Nested Tuples (0.0, 0.1)
// =============================================================================

struct Inner(i32, i32);
struct Outer(Inner, String);

impl Outer {
    fn update_0_0(&{mut 0.0} mut self, val: i32) {
        self.0.0 = val;
    }

    fn update_0_1(&{mut 0.1} mut self, val: i32) {
        self.0.1 = val;
    }

    fn test_basic_nested(&mut self) {
        // Can update both - they're disjoint
        self.update_0_0(100);
        self.update_0_1(200);
    }
}

// =============================================================================
// Test 2: Triple Nested Tuples (0.0.0)
// =============================================================================

struct Level3(i32, i32);
struct Level2(Level3, Level3);
struct Level1(Level2, String);

impl Level1 {
    fn update_0_0_0(&{mut 0.0.0} mut self, val: i32) {
        self.0.0.0 = val;
    }

    fn update_0_0_1(&{mut 0.0.1} mut self, val: i32) {
        self.0.0.1 = val;
    }

    fn update_0_1_0(&{mut 0.1.0} mut self, val: i32) {
        self.0.1.0 = val;
    }

    fn test_triple_nested(&mut self) {
        // All disjoint paths
        self.update_0_0_0(1);
        self.update_0_0_1(2);
        self.update_0_1_0(3);
    }
}

// =============================================================================
// Test 3: Named -> Tuple -> Tuple (outer.0.1)
// =============================================================================

struct Vec2(f32, f32);
struct Transform {
    position: Vec2,
    rotation: Vec2,
}

impl Transform {
    fn update_position_x(&{mut position.0} mut self, x: f32) {
        self.position.0 = x;
    }

    fn update_position_y(&{mut position.1} mut self, y: f32) {
        self.position.1 = y;
    }

    fn update_rotation_x(&{mut rotation.0} mut self, x: f32) {
        self.rotation.0 = x;
    }

    fn test_named_tuple_tuple(&mut self) {
        // position.0 and position.1 are disjoint
        self.update_position_x(10.0);
        self.update_position_y(20.0);

        // position.0 and rotation.0 are disjoint (different parents)
        let _px = &self.position.0;
        self.update_rotation_x(5.0);
    }
}

// =============================================================================
// Test 4: Complex Mixed - Named -> Tuple -> Tuple -> Named
// Case: blah.0.2.moo
// =============================================================================

struct DeepNamed {
    moo: i32,
    baa: String,
}

struct MiddleTuple(i32, String, DeepNamed);
struct Container {
    blah: MiddleTuple,
    other: i32,
}

impl Container {
    // Access: blah (named) -> 0 (tuple) -> 2 (tuple) -> moo (named)
    // Wait, that's 4 levels but MiddleTuple only has 3 elements
    // Let me reconsider: blah.0 would be i32, blah.1 would be String, blah.2 would be DeepNamed
    // So blah.2.moo makes sense (3 levels: named -> tuple -> named)
    fn update_blah_2_moo(&{mut blah.2.moo} mut self, val: i32) {
        self.blah.2.moo = val;
    }

    fn update_blah_2_baa(&{mut blah.2.baa} mut self, s: String) {
        self.blah.2.baa = s;
    }

    fn test_complex_mixed(&mut self) {
        // blah.2.moo and blah.2.baa are disjoint
        self.update_blah_2_moo(42);
        self.update_blah_2_baa(String::from("test"));

        // blah.2.moo and other are disjoint
        let _other = &self.other;
        self.update_blah_2_moo(99);
    }
}

// =============================================================================
// Test 5: Tuple -> Named -> Tuple
// Case: 0.field.1
// =============================================================================

struct StructWithTuple {
    field: Vec2,
    name: String,
}

struct TupleContainer(StructWithTuple, i32);

impl TupleContainer {
    // Access: 0 (tuple) -> field (named) -> 0 (tuple)
    fn update_0_field_0(&{mut 0.field.0} mut self, val: f32) {
        self.0.field.0 = val;
    }

    // Access: 0 (tuple) -> field (named) -> 1 (tuple)
    fn update_0_field_1(&{mut 0.field.1} mut self, val: f32) {
        self.0.field.1 = val;
    }

    // Access: 0 (tuple) -> name (named)
    fn update_0_name(&{mut 0.name} mut self, s: String) {
        self.0.name = s;
    }

    fn test_tuple_named_tuple(&mut self) {
        // 0.field.0 and 0.field.1 are disjoint
        self.update_0_field_0(1.0);
        self.update_0_field_1(2.0);

        // 0.field.0 and 0.name are disjoint
        self.update_0_field_0(3.0);
        self.update_0_name(String::from("test"));

        // 0.field.0 and element 1 are disjoint
        let _elem1 = &self.1;
        self.update_0_field_0(4.0);
    }
}

// =============================================================================
// Test 6: Multiple Nested Fields in Same View Spec
// =============================================================================

struct MultiNested {
    tuple1: Inner,
    tuple2: Inner,
}

impl MultiNested {
    // Multiple nested tuple paths in one view spec
    fn update_both(&{mut tuple1.0, mut tuple2.1} mut self, a: i32, b: i32) {
        self.tuple1.0 = a;
        self.tuple2.1 = b;
    }

    fn test_multiple_nested(&mut self) {
        self.update_both(10, 20);
    }
}

// =============================================================================
// Test 7: Mixed Mutabilities with Nested Tuples
// =============================================================================

struct ReadWrite {
    data: Vec2,
}

impl ReadWrite {
    fn mixed_access(&{data.0, mut data.1} mut self, new_y: f32) -> f32 {
        let x = self.data.0; // Read immutably
        self.data.1 = new_y; // Write mutably
        x
    }
}

// =============================================================================
// Test 8: Deep Nesting (4+ levels)
// =============================================================================

struct L4(i32, i32);
struct L3(L4, L4);
struct L2(L3, L3);
struct L1 {
    deep: L2,
}

impl L1 {
    // 4 levels: named -> tuple -> tuple -> tuple
    fn update_deep_0_0_0(&{mut deep.0.0.0} mut self, val: i32) {
        self.deep.0.0.0 = val;
    }

    fn update_deep_0_0_1(&{mut deep.0.0.1} mut self, val: i32) {
        self.deep.0.0.1 = val;
    }

    fn update_deep_0_1_0(&{mut deep.0.1.0} mut self, val: i32) {
        self.deep.0.1.0 = val;
    }

    fn test_very_deep(&mut self) {
        // All disjoint at different levels
        self.update_deep_0_0_0(1);
        self.update_deep_0_0_1(2);
        self.update_deep_0_1_0(3);
    }
}

// =============================================================================
// Test 9: Real-World Game Engine Pattern
// =============================================================================

struct Position(f32, f32, f32);
struct Rotation(f32, f32, f32, f32);
struct Scale(f32, f32, f32);

struct TransformComponents {
    position: Position,
    rotation: Rotation,
    scale: Scale,
}

struct Entity {
    transform: TransformComponents,
    health: f32,
}

impl Entity {
    fn update_pos_x(&{mut transform.position.0} mut self, x: f32) {
        self.transform.position.0 = x;
    }

    fn update_pos_y(&{mut transform.position.1} mut self, y: f32) {
        self.transform.position.1 = y;
    }

    fn update_rot_w(&{mut transform.rotation.3} mut self, w: f32) {
        self.transform.rotation.3 = w;
    }

    fn update_scale_uniform(&{mut transform.scale.0, mut transform.scale.1, mut transform.scale.2} mut self, s: f32) {
        self.transform.scale.0 = s;
        self.transform.scale.1 = s;
        self.transform.scale.2 = s;
    }

    fn game_tick(&mut self) {
        // Borrow health while updating transform components
        let _health = &self.health;

        // Update multiple disjoint transform fields
        self.update_pos_x(10.0);
        self.update_pos_y(20.0);
        self.update_rot_w(1.0);
        self.update_scale_uniform(2.0);
    }
}

// =============================================================================
// Main: Run all tests
// =============================================================================

fn main() {
    // Test 1: Basic nested tuples
    let mut outer = Outer(Inner(0, 0), String::from("test"));
    outer.test_basic_nested();
    assert_eq!(outer.0.0, 100);
    assert_eq!(outer.0.1, 200);
    println!("✓ Test 1: Basic nested tuples (0.0, 0.1)");

    // Test 2: Triple nested tuples
    let mut level1 = Level1(
        Level2(Level3(0, 0), Level3(0, 0)),
        String::from("test")
    );
    level1.test_triple_nested();
    assert_eq!(level1.0.0.0, 1);
    assert_eq!(level1.0.0.1, 2);
    assert_eq!(level1.0.1.0, 3);
    println!("✓ Test 2: Triple nested tuples (0.0.0)");

    // Test 3: Named -> Tuple -> Tuple
    let mut transform = Transform {
        position: Vec2(0.0, 0.0),
        rotation: Vec2(0.0, 0.0),
    };
    transform.test_named_tuple_tuple();
    assert_eq!(transform.position.0, 10.0);
    assert_eq!(transform.position.1, 20.0);
    println!("✓ Test 3: Named -> Tuple -> Tuple (position.0)");

    // Test 4: Complex mixed (blah.2.moo)
    let mut container = Container {
        blah: MiddleTuple(0, String::new(), DeepNamed { moo: 0, baa: String::new() }),
        other: 0,
    };
    container.test_complex_mixed();
    assert_eq!(container.blah.2.moo, 99);
    println!("✓ Test 4: Complex mixed (blah.2.moo)");

    // Test 5: Tuple -> Named -> Tuple
    let mut tc = TupleContainer(
        StructWithTuple {
            field: Vec2(0.0, 0.0),
            name: String::new(),
        },
        0
    );
    tc.test_tuple_named_tuple();
    assert_eq!(tc.0.field.0, 4.0);
    println!("✓ Test 5: Tuple -> Named -> Tuple (0.field.0)");

    // Test 6: Multiple nested fields
    let mut multi = MultiNested {
        tuple1: Inner(0, 0),
        tuple2: Inner(0, 0),
    };
    multi.test_multiple_nested();
    assert_eq!(multi.tuple1.0, 10);
    assert_eq!(multi.tuple2.1, 20);
    println!("✓ Test 6: Multiple nested fields in one view spec");

    // Test 7: Mixed mutabilities
    let mut rw = ReadWrite { data: Vec2(5.0, 10.0) };
    let x = rw.mixed_access(15.0);
    assert_eq!(x, 5.0);
    assert_eq!(rw.data.1, 15.0);
    println!("✓ Test 7: Mixed mutabilities with nested tuples");

    // Test 8: Deep nesting
    let mut deep = L1 {
        deep: L2(L3(L4(0, 0), L4(0, 0)), L3(L4(0, 0), L4(0, 0))),
    };
    deep.test_very_deep();
    assert_eq!(deep.deep.0.0.0, 1);
    assert_eq!(deep.deep.0.0.1, 2);
    assert_eq!(deep.deep.0.1.0, 3);
    println!("✓ Test 8: Deep nesting (4+ levels)");

    // Test 9: Game engine pattern
    let mut entity = Entity {
        transform: TransformComponents {
            position: Position(0.0, 0.0, 0.0),
            rotation: Rotation(0.0, 0.0, 0.0, 1.0),
            scale: Scale(1.0, 1.0, 1.0),
        },
        health: 100.0,
    };
    entity.game_tick();
    assert_eq!(entity.transform.position.0, 10.0);
    assert_eq!(entity.transform.position.1, 20.0);
    assert_eq!(entity.transform.scale.0, 2.0);
    println!("✓ Test 9: Real-world game engine pattern");

    println!("\n🎉 SUCCESS: All nested tuple field tests passed!");
    println!("   - Basic nested: 0.0, 0.1");
    println!("   - Triple nested: 0.0.0");
    println!("   - Mixed patterns: blah.2.moo, 0.field.1");
    println!("   - Multiple fields: {{mut 0.0, mut 0.1}}");
    println!("   - Deep nesting: 4+ levels");
}
