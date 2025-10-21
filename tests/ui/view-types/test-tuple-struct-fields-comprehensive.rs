//@ check-pass
#![feature(view_types)]
#![allow(unused, incomplete_features)]

// TEST: Tuple Struct Fields - Comprehensive Coverage (Single-Level)
//
// PURPOSE: Verify that view types work correctly with tuple struct fields
// using numeric syntax (0, 1, 2, etc.) for field access.
//
// THEOREMS (formalization/Core_Proven.v):
// - different_fields_no_conflict: Different fields never conflict (applies to numeric fields)
// - same_field_mut_conflicts: Mutable accesses conflict (applies to tuple fields)
// - same_field_imm_no_conflict: Immutable accesses don't conflict (applies to tuple fields)
//
// SCOPE: Single-level tuple fields only. Nested tuple fields (0.0, 0.1) are deferred
// to V2 due to lexer complexity (0.0 is tokenized as float literal).
//
// RATIONALE:
// Tuple structs are common in Rust for:
// - Newtype pattern: wrapping a single value
// - Simple data structures: Point(x, y), Color(r, g, b)
// - Generic pairs/triples: Pair<T, U>, Triple<A, B, C>
//
// NOTE: This tests tuple STRUCTS (named types with methods), not tuple TYPES
// (anonymous tuples which should be destructured instead).

// =============================================================================
// Test 1: Newtype Pattern - Single Field
// =============================================================================

struct Counter(u32);

impl Counter {
    fn increment(&{mut 0} mut self) {
        self.0 += 1;
    }

    fn get(&{0} self) -> u32 {
        self.0
    }

    fn reset(&{mut 0} mut self) {
        self.0 = 0;
    }

    fn add(&{mut 0} mut self, amount: u32) {
        self.0 += amount;
    }

    fn test_newtype(&mut self) {
        self.increment();
        let val = self.get();
        assert_eq!(val, 1);
        self.add(5);
        assert_eq!(self.get(), 6);
    }
}

struct Meters(f32);

impl Meters {
    fn new(value: f32) -> Self {
        Meters(value)
    }

    fn add(&{mut 0} mut self, other: f32) {
        self.0 += other;
    }

    fn scale(&{mut 0} mut self, factor: f32) {
        self.0 *= factor;
    }

    fn value(&{0} self) -> f32 {
        self.0
    }
}

// =============================================================================
// Test 2: Two-Field Tuple Struct (Point Pattern)
// =============================================================================

struct Point2D(f32, f32);

impl Point2D {
    fn set_x(&{mut 0} mut self, x: f32) {
        self.0 = x;
    }

    fn set_y(&{mut 1} mut self, y: f32) {
        self.1 = y;
    }

    fn get_x(&{0} self) -> f32 {
        self.0
    }

    fn get_y(&{1} self) -> f32 {
        self.1
    }

    fn move_by(&{mut 0, mut 1} mut self, dx: f32, dy: f32) {
        self.0 += dx;
        self.1 += dy;
    }

    fn test_disjoint(&mut self) {
        self.set_x(10.0);  // Mutable borrow of field 0
        self.set_y(20.0);  // Mutable borrow of field 1 - disjoint!
    }
}

// =============================================================================
// Test 3: Three-Field Tuple Struct
// =============================================================================

struct Point3D(f32, f32, f32);

impl Point3D {
    fn set_x(&{mut 0} mut self, x: f32) {
        self.0 = x;
    }

    fn set_y(&{mut 1} mut self, y: f32) {
        self.1 = y;
    }

    fn set_z(&{mut 2} mut self, z: f32) {
        self.2 = z;
    }

    fn move_xy(&{mut 0, mut 1} mut self, dx: f32, dy: f32) {
        self.0 += dx;
        self.1 += dy;
    }

    fn move_xyz(&{mut 0, mut 1, mut 2} mut self, dx: f32, dy: f32, dz: f32) {
        self.0 += dx;
        self.1 += dy;
        self.2 += dz;
    }

    fn scale_x_by_y(&{mut 0, 1} mut self) {
        self.0 *= self.1;
    }

    fn test_three_fields(&mut self) {
        self.set_x(1.0);
        self.set_y(2.0);
        self.set_z(3.0);
        self.scale_x_by_y();
        assert_eq!(self.0, 2.0); // 1.0 * 2.0
    }
}

// =============================================================================
// Test 4: Multi-Field Tuple Struct (5+ fields)
// =============================================================================

struct Color(u8, u8, u8, u8, String); // RGBA + name

impl Color {
    fn set_red(&{mut 0} mut self, r: u8) {
        self.0 = r;
    }

    fn set_green(&{mut 1} mut self, g: u8) {
        self.1 = g;
    }

    fn set_blue(&{mut 2} mut self, b: u8) {
        self.2 = b;
    }

    fn set_alpha(&{mut 3} mut self, a: u8) {
        self.3 = a;
    }

    fn set_name(&{mut 4} mut self, name: String) {
        self.4 = name;
    }

    fn set_rgb(&{mut 0, mut 1, mut 2} mut self, r: u8, g: u8, b: u8) {
        self.0 = r;
        self.1 = g;
        self.2 = b;
    }

    fn get_rgb(&{0, 1, 2} self) -> (u8, u8, u8) {
        (self.0, self.1, self.2)
    }

    fn test_multi_field(&mut self) {
        self.set_rgb(255, 128, 64);
        self.set_alpha(200);
        self.set_name(String::from("orange"));
        let (r, g, b) = self.get_rgb();
        assert_eq!((r, g, b), (255, 128, 64));
    }
}

// =============================================================================
// Test 5: Generic Pair
// =============================================================================

struct Pair<T, U>(T, U);

impl<T, U> Pair<T, U> {
    fn set_first(&{mut 0} mut self, value: T) {
        self.0 = value;
    }

    fn set_second(&{mut 1} mut self, value: U) {
        self.1 = value;
    }

    fn update_both(&{mut 0, mut 1} mut self, first: T, second: U) {
        self.0 = first;
        self.1 = second;
    }

    fn get_first_copy(&{0} self) -> T
    where
        T: Copy,
    {
        self.0
    }

    fn get_second_copy(&{1} self) -> U
    where
        U: Copy,
    {
        self.1
    }
}

impl<T: Clone> Pair<T, T> {
    fn swap(&{mut 0, mut 1} mut self) {
        let temp = self.0.clone();
        self.0 = self.1.clone();
        self.1 = temp;
    }
}

// =============================================================================
// Test 6: Subview Subsumption with Tuple Fields
// =============================================================================

struct Vector3(f32, f32, f32);

impl Vector3 {
    fn set_x(&{mut 0} mut self, x: f32) {
        self.0 = x;
    }

    fn set_xy(&{mut 0, mut 1} mut self, x: f32, y: f32) {
        self.0 = x;
        self.1 = y;
    }

    fn set_xyz(&{mut 0, mut 1, mut 2} mut self, x: f32, y: f32, z: f32) {
        // Can call smaller view methods (subview subsumption)
        self.set_xy(x, y);
        self.2 = z;
    }

    fn normalize(&{mut 0, mut 1, mut 2} mut self) {
        let len = (self.0 * self.0 + self.1 * self.1 + self.2 * self.2).sqrt();
        if len > 0.0 {
            self.0 /= len;
            self.1 /= len;
            self.2 /= len;
        }
    }

    fn test_subview(&mut self) {
        self.set_xyz(3.0, 4.0, 0.0);
        // Subview: set_x called from set_xy called from set_xyz
        self.normalize();
        let len = (self.0 * self.0 + self.1 * self.1 + self.2 * self.2).sqrt();
        assert!((len - 1.0).abs() < 0.0001);
    }
}

// =============================================================================
// Test 7: Iterator Patterns with Tuple Fields
// =============================================================================

struct Stats(i32, i32, i32); // min, max, count

impl Stats {
    fn update_min(&{mut 0} mut self, value: i32) {
        if value < self.0 {
            self.0 = value;
        }
    }

    fn update_max(&{mut 1} mut self, value: i32) {
        if value > self.1 {
            self.1 = value;
        }
    }

    fn increment_count(&{mut 2} mut self) {
        self.2 += 1;
    }

    fn process_values(&mut self, values: Vec<i32>) {
        values.iter().for_each(|&v| {
            self.update_min(v);
            self.update_max(v);
            self.increment_count();
        });
    }
}

// =============================================================================
// Test 8: Mixed Mutability with Tuple Fields
// =============================================================================

struct Processor(Vec<i32>, Vec<i32>, u32); // input, output, processed_count

impl Processor {
    fn process_item(&{0, mut 1, mut 2} mut self) -> Option<i32> {
        if self.2 < self.0.len() as u32 {
            let value = self.0[self.2 as usize];
            self.1.push(value * 2);
            self.2 += 1;
            Some(value)
        } else {
            None
        }
    }

    fn reset_output(&{mut 1} mut self) {
        self.1.clear();
    }

    fn reset_count(&{mut 2} mut self) {
        self.2 = 0;
    }

    fn test_mixed(&mut self) {
        while let Some(_) = self.process_item() {
            // Process all items
        }
        assert_eq!(self.1.len(), 3);
        assert_eq!(self.2, 3);
    }
}

// =============================================================================
// Test 9: Real-World Pattern - RGB Color Operations
// =============================================================================

struct RGB(u8, u8, u8);

impl RGB {
    fn set_red(&{mut 0} mut self, r: u8) {
        self.0 = r;
    }

    fn set_green(&{mut 1} mut self, g: u8) {
        self.1 = g;
    }

    fn set_blue(&{mut 2} mut self, b: u8) {
        self.2 = b;
    }

    fn get_red(&{0} self) -> u8 {
        self.0
    }

    fn get_green(&{1} self) -> u8 {
        self.1
    }

    fn get_blue(&{2} self) -> u8 {
        self.2
    }

    fn brighten_red(&{0, mut 1, mut 2} mut self) {
        let factor = self.0 as f32 / 255.0;
        self.1 = ((self.1 as f32 * factor) as u8).min(255);
        self.2 = ((self.2 as f32 * factor) as u8).min(255);
    }

    fn set_all(&{mut 0, mut 1, mut 2} mut self, r: u8, g: u8, b: u8) {
        self.0 = r;
        self.1 = g;
        self.2 = b;
    }

    fn grayscale(&{0, 1, 2} self) -> u8 {
        ((self.0 as u32 + self.1 as u32 + self.2 as u32) / 3) as u8
    }
}

// =============================================================================
// Test 10: Disjoint Field Borrowing
// =============================================================================

struct Entity(f32, f32, f32, f32); // x, y, vx, vy

impl Entity {
    fn update_position(&{mut 0, mut 1, 2, 3} mut self, dt: f32) {
        self.0 += self.2 * dt;  // x += vx * dt
        self.1 += self.3 * dt;  // y += vy * dt
    }

    fn set_velocity(&{mut 2, mut 3} mut self, vx: f32, vy: f32) {
        self.2 = vx;
        self.3 = vy;
    }

    fn get_position(&{0, 1} self) -> (f32, f32) {
        (self.0, self.1)
    }

    fn get_velocity(&{2, 3} self) -> (f32, f32) {
        (self.2, self.3)
    }

    fn test_disjoint(&mut self) {
        self.set_velocity(1.0, 2.0);     // Fields 2, 3
        self.update_position(1.0);       // Fields 0, 1, 2, 3 (mixed)
        let pos = self.get_position();   // Fields 0, 1
        assert_eq!(pos.0, 1.0);
    }
}

// =============================================================================
// Test 11: Two Immutable Readers of Same Tuple Field
// =============================================================================

struct ReadOnly(i32, i32, i32);

impl ReadOnly {
    fn read_first_a(&{0} self) -> i32 {
        self.0
    }

    fn read_first_b(&{0} self) -> i32 {
        self.0
    }

    fn read_all(&{0, 1, 2} self) -> (i32, i32, i32) {
        (self.0, self.1, self.2)
    }

    fn test_two_readers(&self) {
        let a = self.read_first_a();
        let b = self.read_first_b();
        assert_eq!(a, b);
    }
}

// =============================================================================
// Test 12: Generic Triple
// =============================================================================

struct Triple<A, B, C>(A, B, C);

impl<A, B, C> Triple<A, B, C> {
    fn set_first(&{mut 0} mut self, value: A) {
        self.0 = value;
    }

    fn set_second(&{mut 1} mut self, value: B) {
        self.1 = value;
    }

    fn set_third(&{mut 2} mut self, value: C) {
        self.2 = value;
    }

    fn update_first_and_second(&{mut 0, mut 1} mut self, first: A, second: B) {
        self.0 = first;
        self.1 = second;
    }

    fn update_all(&{mut 0, mut 1, mut 2} mut self, first: A, second: B, third: C) {
        // Subview: {0, 1} ⊆ {0, 1, 2}
        self.update_first_and_second(first, second);
        self.2 = third;
    }

    fn get_first_copy(&{0} self) -> A
    where
        A: Copy,
    {
        self.0
    }

    fn get_all_copy(&{0, 1, 2} self) -> (A, B, C)
    where
        A: Copy,
        B: Copy,
        C: Copy,
    {
        (self.0, self.1, self.2)
    }
}

// =============================================================================
// Test 13: Accumulator with Closures
// =============================================================================

struct Accumulator(i32, i32); // sum, count

impl Accumulator {
    fn add(&{mut 0} mut self, value: i32) {
        self.0 += value;
    }

    fn increment_count(&{mut 1} mut self) {
        self.1 += 1;
    }

    fn process_values(&mut self, values: Vec<i32>) {
        values.iter().for_each(|&v| {
            self.add(v);
            self.increment_count();
        });
    }
}

// =============================================================================
// Test 14: Match Expressions with Tuple Fields
// =============================================================================

enum Command {
    SetFirst(i32),
    SetSecond(i32),
    Reset,
}

struct MutablePair(i32, i32);

impl MutablePair {
    fn set_first(&{mut 0} mut self, value: i32) {
        self.0 = value;
    }

    fn set_second(&{mut 1} mut self, value: i32) {
        self.1 = value;
    }

    fn reset(&{mut 0, mut 1} mut self) {
        self.0 = 0;
        self.1 = 0;
    }

    fn handle_command(&mut self, cmd: Command) {
        match cmd {
            Command::SetFirst(v) => self.set_first(v),
            Command::SetSecond(v) => self.set_second(v),
            Command::Reset => self.reset(),
        }
    }
}

// =============================================================================
// Test 15: Reborrowing with Tuple Fields
// =============================================================================

struct Data(i32, i32, i32);

impl Data {
    fn update_0(&{mut 0} mut self, value: i32) {
        self.0 = value;
    }

    fn update_1(&{mut 1} mut self, value: i32) {
        self.1 = value;
    }

    fn update_2(&{mut 2} mut self, value: i32) {
        self.2 = value;
    }
}

fn helper_0(data: &mut Data, value: i32) {
    data.update_0(value);
}

fn helper_1(data: &mut Data, value: i32) {
    data.update_1(value);
}

fn update_all_via_helpers(data: &mut Data) {
    helper_0(&mut *data, 10);
    helper_1(&mut *data, 20);
    data.update_2(30);
}

// =============================================================================
// Test 16: Large Tuple Struct (10 fields)
// =============================================================================

struct LargeTuple(i32, i32, i32, i32, i32, i32, i32, i32, i32, i32);

impl LargeTuple {
    fn update_field(&{mut 0, mut 1, mut 2, mut 3, mut 4, mut 5, mut 6, mut 7, mut 8, mut 9} mut self, index: usize, value: i32) {
        match index {
            0 => self.0 = value,
            1 => self.1 = value,
            2 => self.2 = value,
            3 => self.3 = value,
            4 => self.4 = value,
            5 => self.5 = value,
            6 => self.6 = value,
            7 => self.7 = value,
            8 => self.8 = value,
            9 => self.9 = value,
            _ => {}
        }
    }

    fn update_subset(&{mut 0, mut 5, mut 9} mut self, a: i32, b: i32, c: i32) {
        self.0 = a;
        self.5 = b;
        self.9 = c;
    }
}

// =============================================================================
// Test 17: Mixed Mutability - Complex
// =============================================================================

struct ComplexMixed(u32, u32, u32, u32); // config1, config2, state1, state2

impl ComplexMixed {
    fn update_states(&{0, 1, mut 2, mut 3} mut self) {
        self.2 = self.0 * 2;
        self.3 = self.1 * 3;
    }

    fn reset_states(&{mut 2, mut 3} mut self) {
        self.2 = 0;
        self.3 = 0;
    }

    fn read_configs(&{0, 1} self) -> (u32, u32) {
        (self.0, self.1)
    }
}

// =============================================================================
// Test 18: Result Pattern with Tuple Fields
// =============================================================================

struct ResultCounter(u32, u32); // success, failure

impl ResultCounter {
    fn increment_success(&{mut 0} mut self) {
        self.0 += 1;
    }

    fn increment_failure(&{mut 1} mut self) {
        self.1 += 1;
    }

    fn handle_results(&mut self, results: Vec<Result<(), String>>) {
        results.into_iter().for_each(|res| match res {
            Ok(_) => self.increment_success(),
            Err(_) => self.increment_failure(),
        });
    }
}

// =============================================================================
// Main Test Driver
// =============================================================================

fn main() {
    // Test 1: Newtype pattern
    let mut counter = Counter(0);
    counter.test_newtype();
    println!("✓ Newtype pattern works");

    let mut meters = Meters::new(10.0);
    meters.add(5.0);
    meters.scale(2.0);
    assert_eq!(meters.value(), 30.0);
    println!("✓ Meters newtype works");

    // Test 2: Point2D
    let mut point2d = Point2D(0.0, 0.0);
    point2d.test_disjoint();
    point2d.move_by(5.0, 10.0);
    assert_eq!(point2d.get_x(), 15.0);
    assert_eq!(point2d.get_y(), 30.0);
    println!("✓ Point2D pattern works");

    // Test 3: Point3D
    let mut point3d = Point3D(1.0, 2.0, 3.0);
    point3d.test_three_fields();
    println!("✓ Point3D pattern works");

    // Test 4: Color
    let mut color = Color(0, 0, 0, 255, String::from("black"));
    color.test_multi_field();
    println!("✓ Multi-field tuple struct works");

    // Test 5: Generic pair
    let mut pair_int_str = Pair(10, String::from("test"));
    pair_int_str.set_first(20);
    pair_int_str.set_second(String::from("updated"));
    println!("✓ Generic Pair works");

    let mut pair_same = Pair(5, 10);
    pair_same.swap();
    assert_eq!(pair_same.0, 10);
    assert_eq!(pair_same.1, 5);
    println!("✓ Pair with swap works");

    // Test 6: Subview
    let mut vec = Vector3(3.0, 4.0, 0.0);
    vec.test_subview();
    println!("✓ Subview subsumption with tuple fields works");

    // Test 7: Stats with iterators
    let mut stats = Stats(i32::MAX, i32::MIN, 0);
    stats.process_values(vec![5, 2, 8, 1, 9]);
    assert_eq!(stats.0, 1);  // min
    assert_eq!(stats.1, 9);  // max
    assert_eq!(stats.2, 5);  // count
    println!("✓ Stats with iterators works");

    // Test 8: Processor with mixed mutability
    let mut proc = Processor(vec![1, 2, 3], vec![], 0);
    proc.test_mixed();
    println!("✓ Processor with mixed mutability works");

    // Test 9: RGB
    let mut rgb = RGB(255, 0, 0);
    rgb.brighten_red();
    println!("✓ RGB color manipulation works");

    // Test 10: Entity disjoint
    let mut entity = Entity(0.0, 0.0, 1.0, 2.0);
    entity.test_disjoint();
    println!("✓ Entity with disjoint fields works");

    // Test 11: Accumulator
    let mut acc = Accumulator(0, 0);
    acc.process_values(vec![1, 2, 3, 4, 5]);
    assert_eq!(acc.0, 15); // sum
    assert_eq!(acc.1, 5);  // count
    println!("✓ Accumulator with closures works");

    // Test 12: ReadOnly
    let readonly = ReadOnly(42, 100, 200);
    readonly.test_two_readers();
    println!("✓ Two immutable readers of same tuple field work");

    // Test 13: Triple
    let mut triple = Triple(1, String::from("two"), 3.0);
    triple.update_all(10, String::from("twenty"), 30.0);
    println!("✓ Generic Triple works");

    // Test 14: Match with tuple fields
    let mut mutable_pair = MutablePair(0, 0);
    mutable_pair.handle_command(Command::SetFirst(10));
    mutable_pair.handle_command(Command::SetSecond(20));
    assert_eq!(mutable_pair.0, 10);
    assert_eq!(mutable_pair.1, 20);
    println!("✓ Match expressions with tuple fields work");

    // Test 15: Reborrowing
    let mut data = Data(0, 0, 0);
    update_all_via_helpers(&mut data);
    assert_eq!(data.0, 10);
    assert_eq!(data.1, 20);
    assert_eq!(data.2, 30);
    println!("✓ Reborrowing with tuple fields works");

    // Test 16: Large tuple
    let mut large = LargeTuple(0, 0, 0, 0, 0, 0, 0, 0, 0, 0);
    large.update_subset(1, 2, 3);
    assert_eq!(large.0, 1);
    assert_eq!(large.5, 2);
    assert_eq!(large.9, 3);
    println!("✓ Large tuple struct (10 fields) works");

    // Test 17: Complex mixed mutability
    let mut complex = ComplexMixed(10, 20, 0, 0);
    complex.update_states();
    assert_eq!(complex.2, 20); // config1 * 2
    assert_eq!(complex.3, 60); // config2 * 3
    println!("✓ Complex mixed mutability works");

    // Test 18: Result counter
    let mut result_counter = ResultCounter(0, 0);
    result_counter.handle_results(vec![Ok(()), Err(String::from("err")), Ok(())]);
    assert_eq!(result_counter.0, 2); // success
    assert_eq!(result_counter.1, 1); // failure
    println!("✓ Result pattern with tuple fields works");

    println!("\n🎉 All tuple struct field tests passed!");
    println!("   ✅ Newtype, Point, RGB, Pair, Triple patterns");
    println!("   ✅ Mixed mutability, disjoint borrowing, subview subsumption");
    println!("   ✅ Iterators, closures, match expressions, reborrowing");
    println!("   ✅ Generic tuples, large tuples (10+ fields)");
    println!("\n   Note: Nested tuple fields (0.0) deferred to V2 due to lexer complexity");
}
