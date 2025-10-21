//@ check-pass
#![feature(view_types)]
#![allow(unused, incomplete_features)]

// DOCUMENTATION EXAMPLES TEST
//
// This test ensures that all examples from the README documentation actually
// compile. If this test fails, it means the documentation is out of sync
// with the implementation.
//
// Each example is copied verbatim from docs/README.md

// =============================================================================
// Example 1: The Motivating Example (from SPLASH 2025 paper)
// =============================================================================

#[derive(Debug)]
struct Item {
    id: usize,
    data: String,
}

fn register_item(_item: &mut Item, id: usize) {
    // Placeholder - would register item with id
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

    fn assign_ids(&mut self) {
        for item in &mut self.data {
            let id = self.new_id();  // ✅ Works with view types!
            register_item(item, id);
        }
    }
}

// =============================================================================
// Example 2: Game Entity (Nested Fields)
// =============================================================================

#[derive(Debug, Clone, Copy)]
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
    name: String,
}

struct GameEvent {
    new_pos: Vec3,
    damage: f32,
}

impl Entity {
    // Access ONLY position, not entire transform
    fn update_position(&{mut transform.position} mut self, pos: Vec3) {
        self.transform.position = pos;
    }

    fn update_health(&{mut health} mut self, damage: f32) {
        self.health -= damage;
    }

    // Can update both simultaneously!
    fn tick(&mut self, events: &[GameEvent]) {
        for event in events {
            self.update_position(event.new_pos);  // Touches transform.position
            self.update_health(event.damage);      // Touches health
            // Both work because they're disjoint!
        }
    }
}

// =============================================================================
// Example 3: Configuration System
// =============================================================================

struct Resolution {
    width: u32,
    height: u32,
}

struct GraphicsSettings {
    resolution: Resolution,
    quality: String,
}

struct AudioSettings {
    volume: f32,
    muted: bool,
}

struct Config {
    graphics: GraphicsSettings,
    audio: AudioSettings,
}

impl Config {
    fn set_resolution(&{mut graphics.resolution} mut self, w: u32, h: u32) {
        self.graphics.resolution.width = w;
        self.graphics.resolution.height = h;
    }

    fn set_volume(&{mut audio.volume} mut self, vol: f32) {
        self.audio.volume = vol;
    }

    // Can call both from one function!
    fn apply_settings(&mut self) {
        self.set_resolution(1920, 1080);
        self.set_volume(0.8);
    }
}

// =============================================================================
// Example from "What Are View Types?" section
// =============================================================================

struct Counter {
    count: usize,
    data: Vec<i32>,
}

impl Counter {
    // View type: this function ONLY accesses count
    fn increment(&{mut count} mut self) -> usize {
        self.count += 1;
        self.count
    }

    fn process(&mut self) {
        for item in &mut self.data {
            // This works! Rust knows increment() only touches count, not data
            let id = self.increment();
            *item = id as i32;
        }
    }
}

// =============================================================================
// Main: Run all documentation examples
// =============================================================================

fn main() {
    // Test Example 1: Motivating example
    let mut s = S {
        next_id: 1,
        data: vec![
            Item { id: 0, data: String::from("first") },
            Item { id: 0, data: String::from("second") },
            Item { id: 0, data: String::from("third") },
        ],
    };
    s.assign_ids();
    assert_eq!(s.next_id, 4);
    assert_eq!(s.data[0].id, 0); // register_item is a no-op in this test
    assert_eq!(s.data[1].id, 0);
    assert_eq!(s.data[2].id, 0);
    println!("✓ Example 1: Motivating example works!");

    // Test Example 2: Game entity
    let mut entity = Entity {
        transform: Transform {
            position: Vec3 { x: 0.0, y: 0.0, z: 0.0 },
            rotation: Vec3 { x: 0.0, y: 0.0, z: 0.0 },
        },
        health: 100.0,
        name: String::from("Player"),
    };
    let events = vec![
        GameEvent {
            new_pos: Vec3 { x: 1.0, y: 2.0, z: 3.0 },
            damage: 10.0,
        },
        GameEvent {
            new_pos: Vec3 { x: 2.0, y: 3.0, z: 4.0 },
            damage: 5.0,
        },
    ];
    entity.tick(&events);
    assert_eq!(entity.transform.position.x, 2.0);
    assert_eq!(entity.transform.position.y, 3.0);
    assert_eq!(entity.transform.position.z, 4.0);
    assert_eq!(entity.health, 85.0);
    println!("✓ Example 2: Game entity works!");

    // Test Example 3: Configuration system
    let mut config = Config {
        graphics: GraphicsSettings {
            resolution: Resolution { width: 800, height: 600 },
            quality: String::from("medium"),
        },
        audio: AudioSettings {
            volume: 0.5,
            muted: false,
        },
    };
    config.apply_settings();
    assert_eq!(config.graphics.resolution.width, 1920);
    assert_eq!(config.graphics.resolution.height, 1080);
    assert_eq!(config.audio.volume, 0.8);
    println!("✓ Example 3: Configuration system works!");

    // Test Counter example
    let mut counter = Counter {
        count: 0,
        data: vec![10, 20, 30],
    };
    counter.process();
    assert_eq!(counter.count, 3);
    assert_eq!(counter.data, vec![1, 2, 3]);
    println!("✓ Counter example works!");

    println!("\n✓ All documentation examples compile and run correctly!");
}
