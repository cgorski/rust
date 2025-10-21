//@ check-pass
#![feature(view_types)]
#![allow(unused, incomplete_features)]

// TRAIT OBJECTS AS FIELDS TEST
//
// This test verifies that view types work correctly when struct fields
// contain trait objects. Note: V1 does not support view types ON trait
// objects (e.g., &{field} dyn Trait), but it DOES support structs that
// CONTAIN trait objects as fields.
//
// Tested patterns:
// - Box<dyn Trait> as field
// - Rc<dyn Trait> as field
// - Arc<dyn Trait> as field
// - Multiple different trait object fields
// - Calling trait methods through view types
// - Disjoint borrowing with trait object fields

use std::fmt::Debug;
use std::rc::Rc;
use std::sync::Arc;

// =============================================================================
// Test 1: Box<dyn Trait> as Field
// =============================================================================

trait Handler {
    fn handle(&self, input: &str) -> String;
}

struct EchoHandler;

impl Handler for EchoHandler {
    fn handle(&self, input: &str) -> String {
        input.to_string()
    }
}

struct UpperHandler;

impl Handler for UpperHandler {
    fn handle(&self, input: &str) -> String {
        input.to_uppercase()
    }
}

struct Service {
    handler: Box<dyn Handler>,
    request_count: usize,
    name: String,
}

impl Service {
    fn new(handler: Box<dyn Handler>, name: String) -> Self {
        Service {
            handler,
            request_count: 0,
            name,
        }
    }

    fn increment_count(&{mut request_count} mut self) {
        self.request_count += 1;
    }

    fn get_count(&{request_count} self) -> usize {
        self.request_count
    }

    fn process(&{handler} self, input: &str) -> String {
        self.handler.handle(input)
    }

    fn get_name(&{name} self) -> String {
        self.name.clone()
    }

    fn set_name(&{mut name} mut self, new_name: String) {
        self.name = new_name;
    }

    // Can access handler and count simultaneously (disjoint fields)
    fn process_and_count(&{handler, request_count} self, input: &str) -> (String, usize) {
        (self.handler.handle(input), self.request_count)
    }
}

// =============================================================================
// Test 2: Multiple Box<dyn Trait> Fields
// =============================================================================

trait Logger {
    fn log(&self, message: &str);
}

struct ConsoleLogger;

impl Logger for ConsoleLogger {
    fn log(&self, message: &str) {
        // Would print to console
    }
}

struct FileLogger;

impl Logger for FileLogger {
    fn log(&self, message: &str) {
        // Would write to file
    }
}

struct Application {
    error_logger: Box<dyn Logger>,
    info_logger: Box<dyn Logger>,
    config: String,
}

impl Application {
    fn log_error(&{error_logger} self, msg: &str) {
        self.error_logger.log(msg);
    }

    fn log_info(&{info_logger} self, msg: &str) {
        self.info_logger.log(msg);
    }

    fn update_config(&{mut config} mut self, new_config: String) {
        self.config = new_config;
    }

    fn get_config(&{config} self) -> String {
        self.config.clone()
    }

    // Can use both loggers simultaneously
    fn log_both(&{error_logger, info_logger} self, msg: &str) {
        self.error_logger.log(msg);
        self.info_logger.log(msg);
    }
}

// =============================================================================
// Test 3: Rc<dyn Trait> as Field
// =============================================================================

trait Renderer {
    fn render(&self) -> String;
}

struct TextRenderer {
    text: String,
}

impl Renderer for TextRenderer {
    fn render(&self) -> String {
        self.text.clone()
    }
}

struct Widget {
    renderer: Rc<dyn Renderer>,
    position: (i32, i32),
    visible: bool,
}

impl Widget {
    fn render(&{renderer} self) -> String {
        self.renderer.render()
    }

    fn set_position(&{mut position} mut self, x: i32, y: i32) {
        self.position = (x, y);
    }

    fn get_position(&{position} self) -> (i32, i32) {
        self.position
    }

    fn set_visible(&{mut visible} mut self, v: bool) {
        self.visible = v;
    }

    fn is_visible(&{visible} self) -> bool {
        self.visible
    }

    fn render_at_position(&{renderer, position} self) -> (String, (i32, i32)) {
        (self.renderer.render(), self.position)
    }
}

// =============================================================================
// Test 4: Arc<dyn Trait> as Field (Thread-Safe)
// =============================================================================

trait DataStore: Send + Sync {
    fn get(&self, key: &str) -> Option<String>;
    fn count(&self) -> usize;
}

struct InMemoryStore;

impl DataStore for InMemoryStore {
    fn get(&self, key: &str) -> Option<String> {
        None // Simplified
    }

    fn count(&self) -> usize {
        0 // Simplified
    }
}

struct Cache {
    store: Arc<dyn DataStore>,
    hits: usize,
    misses: usize,
}

impl Cache {
    fn increment_hits(&{mut hits} mut self) {
        self.hits += 1;
    }

    fn increment_misses(&{mut misses} mut self) {
        self.misses += 1;
    }

    fn get_stats(&{hits, misses} self) -> (usize, usize) {
        (self.hits, self.misses)
    }

    fn query(&{store} self, key: &str) -> Option<String> {
        self.store.get(key)
    }

    fn store_count(&{store} self) -> usize {
        self.store.count()
    }

    fn query_and_stats(&{store, hits, misses} self, key: &str) -> (Option<String>, usize, usize) {
        (self.store.get(key), self.hits, self.misses)
    }
}

// =============================================================================
// Test 5: Trait Objects with Lifetimes
// =============================================================================

trait Validator<'a> {
    fn validate(&self, data: &'a str) -> bool;
}

struct LengthValidator {
    max_length: usize,
}

impl<'a> Validator<'a> for LengthValidator {
    fn validate(&self, data: &'a str) -> bool {
        data.len() <= self.max_length
    }
}

struct Form<'a> {
    validator: Box<dyn Validator<'a> + 'a>,
    data: String,
    submitted: bool,
}

impl<'a> Form<'a> {
    fn set_data(&{mut data} mut self, new_data: String) {
        self.data = new_data;
    }

    fn get_data(&{data} self) -> String {
        self.data.clone()
    }

    fn mark_submitted(&{mut submitted} mut self) {
        self.submitted = true;
    }

    fn is_submitted(&{submitted} self) -> bool {
        self.submitted
    }
}

// =============================================================================
// Test 6: Multiple Trait Bounds
// =============================================================================

trait Serialize {
    fn serialize(&self) -> Vec<u8>;
}

trait Deserialize {
    fn deserialize(data: &[u8]) -> Self where Self: Sized;
}

struct SerializableHandler {
    data: Vec<u8>,
}

impl Serialize for SerializableHandler {
    fn serialize(&self) -> Vec<u8> {
        self.data.clone()
    }
}

impl Handler for SerializableHandler {
    fn handle(&self, input: &str) -> String {
        input.to_string()
    }
}

struct Processor {
    handler: Box<dyn Handler>,
    serializer: Box<dyn Serialize>,
    buffer: Vec<u8>,
}

impl Processor {
    fn process(&{handler} self, input: &str) -> String {
        self.handler.handle(input)
    }

    fn serialize(&{serializer} self) -> Vec<u8> {
        self.serializer.serialize()
    }

    fn write_buffer(&{mut buffer} mut self, data: Vec<u8>) {
        self.buffer = data;
    }

    fn read_buffer(&{buffer} self) -> Vec<u8> {
        self.buffer.clone()
    }

    fn process_and_buffer(&{handler, buffer} self, input: &str) -> (String, usize) {
        (self.handler.handle(input), self.buffer.len())
    }
}

// =============================================================================
// Test 7: Debug Trait Object
// =============================================================================

struct Debuggable {
    debug: Box<dyn Debug>,
    name: String,
    id: usize,
}

impl Debuggable {
    fn get_name(&{name} self) -> String {
        self.name.clone()
    }

    fn get_id(&{id} self) -> usize {
        self.id
    }

    fn set_id(&{mut id} mut self, new_id: usize) {
        self.id = new_id;
    }
}

// =============================================================================
// Test 8: Real-World Pattern - Plugin System
// =============================================================================

trait Plugin {
    fn name(&self) -> &str;
    fn execute(&self, args: &[String]) -> Result<String, String>;
}

struct GreetPlugin;

impl Plugin for GreetPlugin {
    fn name(&self) -> &str {
        "greet"
    }

    fn execute(&self, args: &[String]) -> Result<String, String> {
        if args.is_empty() {
            Ok(String::from("Hello, World!"))
        } else {
            Ok(format!("Hello, {}!", args[0]))
        }
    }
}

struct PluginManager {
    plugins: Vec<Box<dyn Plugin>>,
    active_count: usize,
    config_path: String,
}

impl PluginManager {
    fn new(config_path: String) -> Self {
        PluginManager {
            plugins: Vec::new(),
            active_count: 0,
            config_path,
        }
    }

    fn add_plugin(&{mut plugins} mut self, plugin: Box<dyn Plugin>) {
        self.plugins.push(plugin);
    }

    fn plugin_count(&{plugins} self) -> usize {
        self.plugins.len()
    }

    fn increment_active(&{mut active_count} mut self) {
        self.active_count += 1;
    }

    fn get_active_count(&{active_count} self) -> usize {
        self.active_count
    }

    fn get_config_path(&{config_path} self) -> String {
        self.config_path.clone()
    }

    fn update_config_path(&{mut config_path} mut self, new_path: String) {
        self.config_path = new_path;
    }

    fn stats(&{plugins, active_count} self) -> (usize, usize) {
        (self.plugins.len(), self.active_count)
    }
}

// =============================================================================
// Test 9: Nested Trait Objects
// =============================================================================

trait Command {
    fn execute(&self) -> i32;
}

struct SimpleCommand {
    value: i32,
}

impl Command for SimpleCommand {
    fn execute(&self) -> i32 {
        self.value
    }
}

struct CommandQueue {
    queue: Vec<Box<dyn Command>>,
}

struct Executor {
    queues: Vec<CommandQueue>,
    result_buffer: Vec<i32>,
    status: String,
}

impl Executor {
    fn add_result(&{mut result_buffer} mut self, result: i32) {
        self.result_buffer.push(result);
    }

    fn get_results(&{result_buffer} self) -> Vec<i32> {
        self.result_buffer.clone()
    }

    fn set_status(&{mut status} mut self, s: String) {
        self.status = s;
    }

    fn get_status(&{status} self) -> String {
        self.status.clone()
    }

    fn queue_count(&{queues} self) -> usize {
        self.queues.len()
    }
}

// =============================================================================
// Test 10: Trait Object with Associated Types
// =============================================================================

trait Iterator2 {
    type Item;
    fn next_item(&mut self) -> Option<Self::Item>;
}

struct Counter {
    count: usize,
}

impl Iterator2 for Counter {
    type Item = usize;

    fn next_item(&mut self) -> Option<usize> {
        self.count += 1;
        Some(self.count)
    }
}

struct IteratorHolder {
    iter: Box<dyn Iterator2<Item = usize>>,
    max_items: usize,
    processed: usize,
}

impl IteratorHolder {
    fn set_max(&{mut max_items} mut self, max: usize) {
        self.max_items = max;
    }

    fn get_max(&{max_items} self) -> usize {
        self.max_items
    }

    fn increment_processed(&{mut processed} mut self) {
        self.processed += 1;
    }

    fn get_processed(&{processed} self) -> usize {
        self.processed
    }

    fn stats(&{max_items, processed} self) -> (usize, usize) {
        (self.max_items, self.processed)
    }
}

// =============================================================================
// Main: Test All Trait Object Patterns
// =============================================================================

fn main() {
    // Test 1: Basic Box<dyn Trait>
    let mut service = Service::new(
        Box::new(EchoHandler),
        String::from("echo-service"),
    );
    service.increment_count();
    assert_eq!(service.get_count(), 1);
    let result = service.process("hello");
    assert_eq!(result, "hello");
    assert_eq!(service.get_name(), "echo-service");
    service.set_name(String::from("new-service"));
    assert_eq!(service.get_name(), "new-service");

    // Test 2: Multiple trait objects
    let app = Application {
        error_logger: Box::new(ConsoleLogger),
        info_logger: Box::new(FileLogger),
        config: String::from("default"),
    };
    app.log_error("error");
    app.log_info("info");
    assert_eq!(app.get_config(), "default");
    app.log_both("both");

    // Test 3: Rc<dyn Trait>
    let mut widget = Widget {
        renderer: Rc::new(TextRenderer {
            text: String::from("rendered"),
        }),
        position: (0, 0),
        visible: true,
    };
    let rendered = widget.render();
    assert_eq!(rendered, "rendered");
    widget.set_position(10, 20);
    assert_eq!(widget.get_position(), (10, 20));
    assert!(widget.is_visible());
    let (text, pos) = widget.render_at_position();
    assert_eq!(text, "rendered");
    assert_eq!(pos, (10, 20));

    // Test 4: Arc<dyn Trait>
    let mut cache = Cache {
        store: Arc::new(InMemoryStore),
        hits: 0,
        misses: 0,
    };
    cache.increment_hits();
    cache.increment_misses();
    let (hits, misses) = cache.get_stats();
    assert_eq!(hits, 1);
    assert_eq!(misses, 1);
    let count = cache.store_count();
    assert_eq!(count, 0);

    // Test 6: Multiple traits
    let mut processor = Processor {
        handler: Box::new(SerializableHandler { data: vec![1, 2, 3] }),
        serializer: Box::new(SerializableHandler { data: vec![4, 5, 6] }),
        buffer: vec![],
    };
    let result = processor.process("test");
    assert_eq!(result, "test");
    let serialized = processor.serialize();
    assert_eq!(serialized, vec![4, 5, 6]);
    processor.write_buffer(vec![7, 8, 9]);
    assert_eq!(processor.read_buffer(), &[7, 8, 9]);

    // Test 7: Debug trait
    let mut debuggable = Debuggable {
        debug: Box::new(42),
        name: String::from("test"),
        id: 1,
    };
    assert_eq!(debuggable.get_name(), "test");
    assert_eq!(debuggable.get_id(), 1);
    debuggable.set_id(2);
    assert_eq!(debuggable.get_id(), 2);

    // Test 8: Plugin system
    let mut pm = PluginManager::new(String::from("/etc/plugins"));
    pm.add_plugin(Box::new(GreetPlugin));
    assert_eq!(pm.plugin_count(), 1);
    pm.increment_active();
    assert_eq!(pm.get_active_count(), 1);
    assert_eq!(pm.get_config_path(), "/etc/plugins");
    pm.update_config_path(String::from("/usr/local/plugins"));
    assert_eq!(pm.get_config_path(), "/usr/local/plugins");
    let (total, active) = pm.stats();
    assert_eq!(total, 1);
    assert_eq!(active, 1);

    // Test 9: Nested trait objects
    let mut executor = Executor {
        queues: vec![],
        result_buffer: vec![],
        status: String::from("idle"),
    };
    executor.add_result(42);
    assert_eq!(executor.get_results(), &[42]);
    executor.set_status(String::from("running"));
    assert_eq!(executor.get_status(), "running");
    assert_eq!(executor.queue_count(), 0);

    // Test 10: Trait with associated types
    let mut holder = IteratorHolder {
        iter: Box::new(Counter { count: 0 }),
        max_items: 100,
        processed: 0,
    };
    holder.set_max(200);
    assert_eq!(holder.get_max(), 200);
    holder.increment_processed();
    assert_eq!(holder.get_processed(), 1);
    let (max, proc) = holder.stats();
    assert_eq!(max, 200);
    assert_eq!(proc, 1);

    println!("✓ All trait object tests passed!");
}
