//@ check-pass
//@ edition: 2021

// Test: Explicit Disjoint Field Borrows (Baseline Rust Behavior)
//
// This test verifies that Rust's borrow checker ALREADY allows simultaneous
// mutable borrows of disjoint fields. This is the foundation that view types
// build upon.
//
// If this passes: The fundamental mechanism exists ✅
// If this fails: We have a bigger problem ❌

struct Counter {
    count: u32,
    data: Vec<String>,
    name: String,
}

// TEST 1: Simultaneous mutable borrows of disjoint fields (should work)
fn test_simultaneous_disjoint_field_borrows() {
    let mut c = Counter {
        count: 0,
        data: vec![],
        name: String::from("test"),
    };

    // THIS IS THE KEY: Can we borrow two different fields at the same time?
    let count_ref = &mut c.count;
    let data_ref = &mut c.data;

    // Use both borrows simultaneously
    *count_ref += 1;
    data_ref.push("item".to_string());

    // This should compile ✅
    assert_eq!(*count_ref, 1);
    assert_eq!(data_ref.len(), 1);
}

// TEST 2: Three simultaneous borrows
fn test_three_simultaneous_borrows() {
    let mut c = Counter {
        count: 0,
        data: vec![],
        name: String::from("initial"),
    };

    let count_ref = &mut c.count;
    let data_ref = &mut c.data;
    let name_ref = &mut c.name;

    *count_ref = 42;
    data_ref.push("test".to_string());
    name_ref.push_str("_updated");

    assert_eq!(*count_ref, 42);
    assert_eq!(data_ref.len(), 1);
    assert_eq!(name_ref, "initial_updated");
}

// TEST 3: Pass disjoint borrows to functions
fn modify_count(count: &mut u32) {
    *count += 1;
}

fn modify_data(data: &mut Vec<String>) {
    data.push("modified".to_string());
}

fn test_pass_disjoint_borrows_to_functions() {
    let mut c = Counter {
        count: 0,
        data: vec![],
        name: String::from("test"),
    };

    let count_ref = &mut c.count;
    let data_ref = &mut c.data;

    // Pass both borrows to different functions
    modify_count(count_ref);
    modify_data(data_ref);

    assert_eq!(*count_ref, 1);
    assert_eq!(data_ref.len(), 1);
}

// TEST 4: Nested struct field borrows
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

fn test_nested_struct_disjoint_borrows() {
    let mut e = Entity {
        transform: Transform {
            position: Vec3 { x: 0.0, y: 0.0, z: 0.0 },
            rotation: Vec3 { x: 0.0, y: 0.0, z: 0.0 },
        },
        health: 100.0,
    };

    // Borrow two different nested fields simultaneously
    let pos_ref = &mut e.transform.position;
    let rot_ref = &mut e.transform.rotation;

    pos_ref.x = 5.0;
    rot_ref.x = 1.0;

    assert_eq!(pos_ref.x, 5.0);
    assert_eq!(rot_ref.x, 1.0);
}

// TEST 5: Disjoint borrows with different depths
fn test_different_depth_borrows() {
    let mut e = Entity {
        transform: Transform {
            position: Vec3 { x: 0.0, y: 0.0, z: 0.0 },
            rotation: Vec3 { x: 0.0, y: 0.0, z: 0.0 },
        },
        health: 100.0,
    };

    // One deep borrow, one shallow borrow - both disjoint
    let pos_x_ref = &mut e.transform.position.x;
    let health_ref = &mut e.health;

    *pos_x_ref = 10.0;
    *health_ref = 50.0;

    assert_eq!(*pos_x_ref, 10.0);
    assert_eq!(*health_ref, 50.0);
}

// TEST 6: The async question - can we return borrows in futures?
use std::future::Future;
use std::pin::Pin;

fn get_count_future(c: &mut Counter) -> impl Future<Output = ()> + '_ {
    let count_borrow = &mut c.count;
    async move {
        *count_borrow += 1;
    }
}

fn get_data_future(c: &mut Counter) -> impl Future<Output = ()> + '_ {
    let data_borrow = &mut c.data;
    async move {
        data_borrow.push("item".to_string());
    }
}

async fn test_futures_with_explicit_borrows() {
    let mut c = Counter {
        count: 0,
        data: vec![],
        name: String::from("test"),
    };

    // Sequential - this works
    get_count_future(&mut c).await;
    get_data_future(&mut c).await;

    // The question: can we create both futures before awaiting?
    // let f1 = get_count_future(&mut c);
    // let f2 = get_data_future(&mut c);  // Would this conflict?
    // f1.await;
    // f2.await;
}

fn main() {
    test_simultaneous_disjoint_field_borrows();
    test_three_simultaneous_borrows();
    test_pass_disjoint_borrows_to_functions();
    test_nested_struct_disjoint_borrows();
    test_different_depth_borrows();

    println!("✅ All explicit disjoint borrow tests passed!");
    println!("This proves Rust's borrow checker supports disjoint field borrows.");
    println!("The challenge is making this work with method call syntax and async.");
}
