// V1 RESTRICTION TEST: Contains method with return reference (expects error)
#![feature(view_types)]
#![allow(unused, incomplete_features)]

// COMPREHENSIVE INTEGRATION TEST
//
// This test combines multiple view type features to ensure they work correctly
// together in realistic scenarios. Each test case represents a real-world
// pattern that exercises multiple capabilities simultaneously.
//
// Features tested in combination:
// - Nested field access + collections
// - Trait objects + disjoint borrowing
// - Generics + lifetimes + view types
// - Interior mutability + view types
// - Complex method composition
// - Multiple levels of nesting
// - Standard library types together

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

// =============================================================================
// Integration Test 1: Game Engine Entity Component System
// Combines: Nested fields, collections, multiple disjoint borrows, trait objects
// =============================================================================

trait Component {
    fn update(&mut self, delta: f32);
    fn name(&self) -> &str;
}

struct PhysicsComponent {
    velocity: (f32, f32),
    acceleration: (f32, f32),
}

impl Component for PhysicsComponent {
    fn update(&mut self, delta: f32) {
        self.velocity.0 += self.acceleration.0 * delta;
        self.velocity.1 += self.acceleration.1 * delta;
    }

    fn name(&self) -> &str {
        "physics"
    }
}

struct RenderComponent {
    sprite_id: usize,
    visible: bool,
}

impl Component for RenderComponent {
    fn update(&mut self, _delta: f32) {
        // Rendering update
    }

    fn name(&self) -> &str {
        "render"
    }
}

struct Transform {
    position: (f32, f32),
    rotation: f32,
    scale: (f32, f32),
}

struct GameObject {
    transform: Transform,
    components: Vec<Box<dyn Component>>,
    tags: Vec<String>,
    active: bool,
}

impl GameObject {
    // Access only position while other fields available separately
    fn move_by(&{mut transform.position} mut self, dx: f32, dy: f32) {
        self.transform.position.0 += dx;
        self.transform.position.1 += dy;
    }

    // Access only rotation
    fn rotate(&{mut transform.rotation} mut self, angle: f32) {
        self.transform.rotation += angle;
    }

    // Access tags independently
    fn add_tag(&{mut tags} mut self, tag: String) {
        self.tags.push(tag);
    }

    fn has_tag(&{tags} self, tag: &str) -> bool {
        self.tags.iter().any(|t| t == tag)
    }

    // Access components independently
    fn component_count(&{components} self) -> usize {
        self.components.len()
    }

    // Toggle active state
    fn set_active(&{mut active} mut self, a: bool) {
        self.active = a;
    }

    fn is_active(&{active} self) -> bool {
        self.active
    }

    // Combine position and active state
    fn position_if_active(&{transform.position, active} self) -> Option<(f32, f32)> {
        if self.active {
            Some(self.transform.position)
        } else {
            None
        }
    }
}

struct GameWorld {
    objects: Vec<GameObject>,
    time: f32,
    paused: bool,
}

impl GameWorld {
    fn increment_time(&{mut time} mut self, delta: f32) {
        self.time += delta;
    }

    fn get_time(&{time} self) -> f32 {
        self.time
    }

    fn set_paused(&{mut paused} mut self, p: bool) {
        self.paused = p;
    }

    fn is_paused(&{paused} self) -> bool {
        self.paused
    }

    fn object_count(&{objects} self) -> usize {
        self.objects.len()
    }
}

// =============================================================================
// Integration Test 2: Web Server Request Handler
// Combines: Collections, interior mutability, trait objects, lifetimes
// =============================================================================

trait Middleware {
    fn process(&self, request: &str) -> String;
}

struct LoggingMiddleware;

impl Middleware for LoggingMiddleware {
    fn process(&self, request: &str) -> String {
        format!("logged: {}", request)
    }
}

struct AuthMiddleware;

impl Middleware for AuthMiddleware {
    fn process(&self, request: &str) -> String {
        format!("authed: {}", request)
    }
}

struct RequestStats {
    total_requests: usize,
    successful: usize,
    failed: usize,
}

struct Server {
    middleware: Vec<Box<dyn Middleware>>,
    routes: HashMap<String, String>,
    stats: RefCell<RequestStats>,
    config: ServerConfig,
}

struct ServerConfig {
    port: u16,
    max_connections: usize,
}

impl Server {
    fn add_middleware(&{mut middleware} mut self, m: Box<dyn Middleware>) {
        self.middleware.push(m);
    }

    fn middleware_count(&{middleware} self) -> usize {
        self.middleware.len()
    }

    fn add_route(&{mut routes} mut self, path: String, handler: String) {
        self.routes.insert(path, handler);
    }

    fn get_route(&{routes} self, path: &str) -> Option<&String> {
        self.routes.get(path)
    }

    fn route_count(&{routes} self) -> usize {
        self.routes.len()
    }

    fn increment_total(&{stats} self) {
        self.stats.borrow_mut().total_requests += 1;
    }

    fn increment_successful(&{stats} self) {
        self.stats.borrow_mut().successful += 1;
    }

    fn get_stats(&{stats} self) -> (usize, usize, usize) {
        let s = self.stats.borrow();
        (s.total_requests, s.successful, s.failed)
    }

    fn set_port(&{mut config.port} mut self, port: u16) {
        self.config.port = port;
    }

    fn get_port(&{config.port} self) -> u16 {
        self.config.port
    }

    fn set_max_connections(&{mut config.max_connections} mut self, max: usize) {
        self.config.max_connections = max;
    }

    fn get_config(&{config} self) -> (u16, usize) {
        (self.config.port, self.config.max_connections)
    }
}

// =============================================================================
// Integration Test 3: Database Connection Pool with Caching
// Combines: Generics, nested structures, RefCell, Rc, complex ownership
// =============================================================================

struct Connection {
    id: usize,
    active: bool,
}

struct QueryCache<T> {
    cache: HashMap<String, T>,
    hits: usize,
    misses: usize,
}

impl<T: Clone> QueryCache<T> {
    fn new() -> Self {
        QueryCache {
            cache: HashMap::new(),
            hits: 0,
            misses: 0,
        }
    }

    fn get(&mut self, key: &str) -> Option<T> {
        if let Some(value) = self.cache.get(key) {
            self.hits += 1;
            Some(value.clone())
        } else {
            self.misses += 1;
            None
        }
    }

    fn insert(&mut self, key: String, value: T) {
        self.cache.insert(key, value);
    }
}

struct ConnectionPool<T> {
    connections: Vec<Connection>,
    cache: RefCell<QueryCache<T>>,
    metrics: PoolMetrics,
}

struct PoolMetrics {
    total_queries: usize,
    active_connections: usize,
}

impl<T: Clone> ConnectionPool<T> {
    fn new() -> Self {
        ConnectionPool {
            connections: Vec::new(),
            cache: RefCell::new(QueryCache::new()),
            metrics: PoolMetrics {
                total_queries: 0,
                active_connections: 0,
            },
        }
    }

    fn add_connection(&{mut connections} mut self, conn: Connection) {
        self.connections.push(conn);
    }

    fn connection_count(&{connections} self) -> usize {
        self.connections.len()
    }

    fn increment_queries(&{mut metrics.total_queries} mut self) {
        self.metrics.total_queries += 1;
    }

    fn get_total_queries(&{metrics.total_queries} self) -> usize {
        self.metrics.total_queries
    }

    fn set_active_connections(&{mut metrics.active_connections} mut self, count: usize) {
        self.metrics.active_connections = count;
    }

    fn get_metrics(&{metrics} self) -> (usize, usize) {
        (self.metrics.total_queries, self.metrics.active_connections)
    }

    fn cache_query(&{cache} self, key: String, value: T) {
        self.cache.borrow_mut().insert(key, value);
    }

    fn get_cached(&{cache} self, key: &str) -> Option<T> {
        self.cache.borrow_mut().get(key)
    }
}

// =============================================================================
// Integration Test 4: UI Framework with Event System
// Combines: Trait objects, nested fields, lifetimes, closures
// =============================================================================

trait EventHandler {
    fn handle_event(&self, event: &str) -> bool;
}

struct ButtonHandler {
    label: String,
}

impl EventHandler for ButtonHandler {
    fn handle_event(&self, event: &str) -> bool {
        event.starts_with("click")
    }
}

struct Layout {
    x: i32,
    y: i32,
    width: u32,
    height: u32,
}

struct Style {
    color: String,
    font_size: u32,
}

struct Widget {
    layout: Layout,
    style: Style,
    handler: Option<Box<dyn EventHandler>>,
    children: Vec<Widget>,
    visible: bool,
}

impl Widget {
    fn set_position(&{mut layout.x, mut layout.y} mut self, x: i32, y: i32) {
        self.layout.x = x;
        self.layout.y = y;
    }

    fn get_position(&{layout.x, layout.y} self) -> (i32, i32) {
        (self.layout.x, self.layout.y)
    }

    fn set_size(&{mut layout.width, mut layout.height} mut self, w: u32, h: u32) {
        self.layout.width = w;
        self.layout.height = h;
    }

    fn get_size(&{layout.width, layout.height} self) -> (u32, u32) {
        (self.layout.width, self.layout.height)
    }

    fn set_color(&{mut style.color} mut self, color: String) {
        self.style.color = color;
    }

    fn get_color(&{style.color} self) -> &str { //~ ERROR view-typed functions cannot return references
        &self.style.color
    }

    fn set_font_size(&{mut style.font_size} mut self, size: u32) {
        self.style.font_size = size;
    }

    fn set_visible(&{mut visible} mut self, v: bool) {
        self.visible = v;
    }

    fn is_visible(&{visible} self) -> bool {
        self.visible
    }

    fn child_count(&{children} self) -> usize {
        self.children.len()
    }

    fn has_handler(&{handler} self) -> bool {
        self.handler.is_some()
    }
}

// =============================================================================
// Integration Test 5: Machine Learning Model with Training State
// Combines: Generics, Vec operations, nested state, statistics tracking
// =============================================================================

struct Hyperparameters {
    learning_rate: f32,
    batch_size: usize,
    epochs: usize,
}

struct TrainingMetrics {
    loss_history: Vec<f32>,
    accuracy_history: Vec<f32>,
    current_epoch: usize,
}

struct Model<T> {
    weights: Vec<T>,
    hyperparams: Hyperparameters,
    metrics: TrainingMetrics,
    trained: bool,
}

impl<T> Model<T> {
    fn set_learning_rate(&{mut hyperparams.learning_rate} mut self, lr: f32) {
        self.hyperparams.learning_rate = lr;
    }

    fn get_learning_rate(&{hyperparams.learning_rate} self) -> f32 {
        self.hyperparams.learning_rate
    }

    fn set_batch_size(&{mut hyperparams.batch_size} mut self, size: usize) {
        self.hyperparams.batch_size = size;
    }

    fn record_loss(&{mut metrics.loss_history} mut self, loss: f32) {
        self.metrics.loss_history.push(loss);
    }

    fn record_accuracy(&{mut metrics.accuracy_history} mut self, acc: f32) {
        self.metrics.accuracy_history.push(acc);
    }

    fn increment_epoch(&{mut metrics.current_epoch} mut self) {
        self.metrics.current_epoch += 1;
    }

    fn current_epoch(&{metrics.current_epoch} self) -> usize {
        self.metrics.current_epoch
    }

    fn loss_count(&{metrics.loss_history} self) -> usize {
        self.metrics.loss_history.len()
    }

    fn mark_trained(&{mut trained} mut self) {
        self.trained = true;
    }

    fn is_trained(&{trained} self) -> bool {
        self.trained
    }

    fn get_hyperparams(&{hyperparams} self) -> (f32, usize, usize) {
        (
            self.hyperparams.learning_rate,
            self.hyperparams.batch_size,
            self.hyperparams.epochs,
        )
    }
}

// =============================================================================
// Main: Run All Integration Tests
// =============================================================================

fn main() {
    println!("Running comprehensive integration tests...\n");

    // Integration Test 1: Game Engine ECS
    {
        let mut obj = GameObject {
            transform: Transform {
                position: (0.0, 0.0),
                rotation: 0.0,
                scale: (1.0, 1.0),
            },
            components: vec![
                Box::new(PhysicsComponent {
                    velocity: (0.0, 0.0),
                    acceleration: (0.0, 9.8),
                }),
            ],
            tags: vec![],
            active: true,
        };

        obj.move_by(10.0, 20.0);
        obj.rotate(3.14);
        obj.add_tag(String::from("player"));
        obj.set_active(true);

        assert_eq!(obj.transform.position, (10.0, 20.0));
        assert!(obj.has_tag("player"));
        assert!(obj.is_active());
        assert_eq!(obj.component_count(), 1);
        assert_eq!(obj.position_if_active(), Some((10.0, 20.0)));

        println!("✓ Integration Test 1: Game Engine ECS passed");
    }

    // Integration Test 2: Web Server
    {
        let mut server = Server {
            middleware: vec![],
            routes: HashMap::new(),
            stats: RefCell::new(RequestStats {
                total_requests: 0,
                successful: 0,
                failed: 0,
            }),
            config: ServerConfig {
                port: 8080,
                max_connections: 100,
            },
        };

        server.add_middleware(Box::new(LoggingMiddleware));
        server.add_route(String::from("/api"), String::from("handler"));
        server.set_port(9000);
        server.increment_total();
        server.increment_successful();

        assert_eq!(server.middleware_count(), 1);
        assert_eq!(server.route_count(), 1);
        assert_eq!(server.get_port(), 9000);
        let (total, success, _) = server.get_stats();
        assert_eq!(total, 1);
        assert_eq!(success, 1);

        println!("✓ Integration Test 2: Web Server passed");
    }

    // Integration Test 3: Database Pool
    {
        let mut pool: ConnectionPool<String> = ConnectionPool::new();

        pool.add_connection(Connection { id: 1, active: true });
        pool.increment_queries();
        pool.cache_query(String::from("SELECT *"), String::from("result"));
        pool.set_active_connections(1);

        assert_eq!(pool.connection_count(), 1);
        assert_eq!(pool.get_total_queries(), 1);
        assert_eq!(pool.get_cached("SELECT *"), Some(String::from("result")));
        let (queries, active) = pool.get_metrics();
        assert_eq!(queries, 1);
        assert_eq!(active, 1);

        println!("✓ Integration Test 3: Database Pool passed");
    }

    // Integration Test 4: UI Framework
    {
        let mut widget = Widget {
            layout: Layout {
                x: 0,
                y: 0,
                width: 100,
                height: 50,
            },
            style: Style {
                color: String::from("blue"),
                font_size: 12,
            },
            handler: Some(Box::new(ButtonHandler {
                label: String::from("Click Me"),
            })),
            children: vec![],
            visible: true,
        };

        widget.set_position(10, 20);
        widget.set_size(200, 100);
        widget.set_color(String::from("red"));
        widget.set_font_size(16);
        widget.set_visible(false);

        assert_eq!(widget.get_position(), (10, 20));
        assert_eq!(widget.get_size(), (200, 100));
        assert_eq!(widget.get_color(), "red");
        assert!(!widget.is_visible());
        assert!(widget.has_handler());

        println!("✓ Integration Test 4: UI Framework passed");
    }

    // Integration Test 5: ML Model
    {
        let mut model: Model<f32> = Model {
            weights: vec![0.1, 0.2, 0.3],
            hyperparams: Hyperparameters {
                learning_rate: 0.01,
                batch_size: 32,
                epochs: 10,
            },
            metrics: TrainingMetrics {
                loss_history: vec![],
                accuracy_history: vec![],
                current_epoch: 0,
            },
            trained: false,
        };

        model.set_learning_rate(0.001);
        model.set_batch_size(64);
        model.record_loss(0.5);
        model.record_accuracy(0.95);
        model.increment_epoch();
        model.mark_trained();

        assert_eq!(model.get_learning_rate(), 0.001);
        assert_eq!(model.current_epoch(), 1);
        assert_eq!(model.loss_count(), 1);
        assert!(model.is_trained());

        println!("✓ Integration Test 5: ML Model passed");
    }

    println!("\n✓✓✓ ALL COMPREHENSIVE INTEGRATION TESTS PASSED! ✓✓✓");
}
