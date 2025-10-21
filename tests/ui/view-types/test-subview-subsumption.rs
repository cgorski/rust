//@ check-pass
#![feature(view_types)]
#![allow(unused, incomplete_features)]

// TEST: Subview Subsumption
//
// THEOREMS (formalization/Core_Proven.v):
// - subview_refl: Subview relation is reflexive (V ⊆ V)
// - subview_trans: Subview relation is transitive (V1 ⊆ V2 ∧ V2 ⊆ V3 → V1 ⊆ V3)
// - subview_preserves_wf: Subview preserves well-formedness
//
// PURPOSE: Test that view-typed methods can call other view-typed methods
// when the callee's view spec is a subview (subset) of the caller's view spec.
//
// RATIONALE:
// If a method M1 has view spec {x, y, z} and calls method M2 with view spec {x, y},
// this should work because M1 has permission to access all fields that M2 needs.
// This is the "subview subsumption" property: a smaller view (subset) can be used
// where a larger view (superset) is available.
//
// Formally: If V1 ⊆ V2 (V1 is subview of V2), then a method with view V2 can call
// a method with view V1, because V2 has all the permissions V1 requires.

// =============================================================================
// Test 1: Single Field Subview - Basic Case
// =============================================================================

struct Point {
    x: f32,
    y: f32,
    z: f32,
}

impl Point {
    // Smallest view: only x
    fn increment_x(&{mut x} mut self) {
        self.x += 1.0;
    }

    // Larger view: x and y
    fn move_xy(&{mut x, mut y} mut self, dx: f32, dy: f32) {
        self.x += dx;
        self.y += dy;

        // Can call increment_x because {x} ⊆ {x, y}
        self.increment_x();
    }

    // Largest view: x, y, and z
    fn move_xyz(&{mut x, mut y, mut z} mut self, dx: f32, dy: f32, dz: f32) {
        self.x += dx;
        self.y += dy;
        self.z += dz;

        // Can call increment_x because {x} ⊆ {x, y, z}
        self.increment_x();

        // Can call move_xy because {x, y} ⊆ {x, y, z}
        self.move_xy(1.0, 1.0);
    }
}

// =============================================================================
// Test 2: Reflexive Subview - Method Can Call Itself
// =============================================================================

struct Counter {
    count: u32,
}

impl Counter {
    fn increment(&{mut count} mut self) {
        if self.count < 100 {
            self.count += 1;
            // Reflexive: {count} ⊆ {count}
            // Method can call itself (recursion with same view spec)
            // Note: Infinite recursion prevented by condition
        }
    }

    fn increment_by(&{mut count} mut self, n: u32) {
        for _ in 0..n {
            // Can call increment because {count} ⊆ {count} (reflexive)
            self.increment();
        }
    }
}

// =============================================================================
// Test 3: Transitive Subview Chain
// =============================================================================

struct Entity {
    id: u32,
    name: String,
    position: (f32, f32),
    velocity: (f32, f32),
    health: f32,
}

impl Entity {
    // Level 1: Single field
    fn increment_id(&{mut id} mut self) {
        self.id += 1;
    }

    // Level 2: Two fields
    fn update_metadata(&{mut id, mut name} mut self) {
        self.id += 1;
        self.name.push_str("_updated");

        // {id} ⊆ {id, name}
        self.increment_id();
    }

    // Level 3: Three fields
    fn update_identity_and_position(&{mut id, mut name, mut position} mut self) {
        self.position.0 += 1.0;

        // {id, name} ⊆ {id, name, position}
        self.update_metadata();

        // {id} ⊆ {id, name, position} (transitive)
        self.increment_id();
    }

    // Level 4: Four fields
    fn full_update(&{mut id, mut name, mut position, mut velocity} mut self) {
        self.velocity.0 += 0.1;

        // {id, name, position} ⊆ {id, name, position, velocity}
        self.update_identity_and_position();

        // {id, name} ⊆ {id, name, position, velocity} (transitive)
        self.update_metadata();

        // {id} ⊆ {id, name, position, velocity} (transitive)
        self.increment_id();
    }
}

// =============================================================================
// Test 4: Mixed Mutability Subviews
// =============================================================================

struct Database {
    cache: Vec<String>,
    metadata: Vec<String>,
    query_count: u32,
    error_count: u32,
}

impl Database {
    // Immutable read of query_count
    fn get_query_count(&{query_count} self) -> u32 {
        self.query_count
    }

    // Mutable query_count, immutable error_count
    fn increment_queries(&{mut query_count, error_count} mut self) {
        self.query_count += 1;

        // Can read error_count (immutable field in our view)
        if self.error_count > 100 {
            // Reset or handle
        }

        // CAN'T call get_query_count here because we have &mut self
        // But the subview relationship still holds conceptually
    }

    // Mutable cache, immutable query_count
    fn update_cache(&{mut cache, query_count} mut self, item: String) {
        self.cache.push(item);

        // Can read query_count (immutable)
        if self.query_count > 0 {
            // Do something
        }
    }

    // Larger view with mixed mutability
    fn process(&{mut cache, mut query_count, error_count} mut self, item: String) {
        // {mut cache, query_count} ⊆ {mut cache, mut query_count, error_count}
        // Note: Mutable is "more permissive" than immutable for same field
        self.update_cache(item);

        // {mut query_count, error_count} ⊆ {mut cache, mut query_count, error_count}
        self.increment_queries();
    }
}

// =============================================================================
// Test 5: Nested Field Path Subviews
// =============================================================================

struct Transform {
    position: Point,
    rotation: Point,
    scale: f32,
}

impl Transform {
    // Access only position.x
    fn nudge_x(&{mut position.x} mut self) {
        self.position.x += 0.1;
    }

    // Access position.x and position.y
    fn nudge_xy(&{mut position.x, mut position.y} mut self) {
        self.position.x += 0.1;
        self.position.y += 0.1;

        // {position.x} ⊆ {position.x, position.y}
        self.nudge_x();
    }

    // Access entire position
    fn reset_position(&{mut position} mut self) {
        self.position.x = 0.0;
        self.position.y = 0.0;
        self.position.z = 0.0;

        // {position.x, position.y} ⊆ {position} (nested subview)
        self.nudge_xy();

        // {position.x} ⊆ {position} (nested subview, transitive)
        self.nudge_x();
    }

    // Access position and rotation
    fn reset_transform(&{mut position, mut rotation} mut self) {
        // {position} ⊆ {position, rotation}
        self.reset_position();

        // Can also directly call nested field methods
        // {position.x, position.y} ⊆ {position, rotation}
        self.nudge_xy();
    }
}

// =============================================================================
// Test 6: Real-World Pattern - Layered System Updates
// =============================================================================

struct GameEntity {
    // Physics
    position: (f32, f32, f32),
    velocity: (f32, f32, f32),

    // Rendering
    sprite_id: u32,
    color: (u8, u8, u8),

    // Gameplay
    health: f32,
    score: u32,
}

impl GameEntity {
    // Physics subsystem: only velocity
    fn apply_gravity(&{mut velocity} mut self, dt: f32) {
        self.velocity.1 -= 9.8 * dt;
    }

    // Physics subsystem: velocity and position
    fn update_physics(&{mut position, mut velocity} mut self, dt: f32) {
        // Apply gravity first (subview: {velocity} ⊆ {position, velocity})
        self.apply_gravity(dt);

        // Then update position
        self.position.0 += self.velocity.0 * dt;
        self.position.1 += self.velocity.1 * dt;
        self.position.2 += self.velocity.2 * dt;
    }

    // Rendering subsystem: sprite and color
    fn update_visual(&{mut sprite_id, mut color} mut self, damaged: bool) {
        if damaged {
            self.color = (255, 0, 0); // Red when damaged
        }
    }

    // Gameplay subsystem: health and score
    fn take_damage(&{mut health, mut score} mut self, damage: f32) {
        self.health -= damage;
        if self.health <= 0.0 {
            self.score = 0; // Reset score on death
        }
    }

    // Full update: calls all subsystems
    fn full_update(&{mut position, mut velocity, mut sprite_id, mut color, mut health, mut score} mut self, dt: f32, damaged: bool, damage: f32) {
        // Physics: {position, velocity} ⊆ full view
        self.update_physics(dt);

        // Rendering: {sprite_id, color} ⊆ full view
        self.update_visual(damaged);

        // Gameplay: {health, score} ⊆ full view
        self.take_damage(damage);

        // Can also call individual methods
        // {velocity} ⊆ full view
        self.apply_gravity(dt);
    }
}

// =============================================================================
// Test 7: Order Independence - Subview Works Regardless of Field Order
// =============================================================================

struct OrderTest {
    a: u32,
    b: u32,
    c: u32,
}

impl OrderTest {
    // View: {a, c} (skips b)
    fn method_ac(&{mut a, mut c} mut self) {
        self.a += 1;
        self.c += 1;
    }

    // View: {a, b, c} in different order
    fn method_cba(&{mut c, mut b, mut a} mut self) {
        // {a, c} ⊆ {c, b, a} (order doesn't matter for subsumption)
        self.method_ac();

        self.b += 1;
    }

    // View: {a, b, c} in another order
    fn method_bac(&{mut b, mut a, mut c} mut self) {
        // {a, c} ⊆ {b, a, c} (order doesn't matter)
        self.method_ac();

        self.b += 1;
    }
}

// =============================================================================
// Main Test Driver
// =============================================================================

fn main() {
    // Test 1: Point - basic subview
    let mut point = Point { x: 0.0, y: 0.0, z: 0.0 };
    point.move_xyz(1.0, 1.0, 1.0);
    println!("✓ Point subview tests passed");

    // Test 2: Counter - reflexive subview
    let mut counter = Counter { count: 0 };
    counter.increment_by(5);
    assert_eq!(counter.count, 5);
    println!("✓ Counter reflexive subview tests passed");

    // Test 3: Entity - transitive subview chain
    let mut entity = Entity {
        id: 1,
        name: "entity".to_string(),
        position: (0.0, 0.0),
        velocity: (0.0, 0.0),
        health: 100.0,
    };
    entity.full_update();
    println!("✓ Entity transitive subview tests passed");

    // Test 4: Database - mixed mutability subviews
    let mut db = Database {
        cache: vec![],
        metadata: vec![],
        query_count: 0,
        error_count: 0,
    };
    db.process("item".to_string());
    println!("✓ Database mixed mutability subview tests passed");

    // Test 5: Transform - nested field path subviews
    let mut transform = Transform {
        position: Point { x: 0.0, y: 0.0, z: 0.0 },
        rotation: Point { x: 0.0, y: 0.0, z: 0.0 },
        scale: 1.0,
    };
    transform.reset_transform();
    println!("✓ Transform nested subview tests passed");

    // Test 6: GameEntity - layered system updates
    let mut game_entity = GameEntity {
        position: (0.0, 10.0, 0.0),
        velocity: (0.0, 0.0, 0.0),
        sprite_id: 1,
        color: (255, 255, 255),
        health: 100.0,
        score: 0,
    };
    game_entity.full_update(0.016, false, 0.0);
    println!("✓ GameEntity layered subview tests passed");

    // Test 7: OrderTest - order independence
    let mut order_test = OrderTest { a: 0, b: 0, c: 0 };
    order_test.method_cba();
    order_test.method_bac();
    println!("✓ OrderTest order independence passed");

    println!("\n🎉 All subview subsumption tests passed!");
    println!("   Validated: reflexive, transitive, mixed mutability, nested paths, order independence");
}
