//@ check-pass
#![feature(view_types)]
#![allow(unused, incomplete_features)]

// PRODUCTION PATTERN: Metrics and Logging During Iteration
//
// This test demonstrates view types solving a CRITICAL production problem:
// tracking metrics/counters while processing data collections.
//
// THE PROBLEM:
// Production services need to:
// 1. Process requests/items in a collection
// 2. Update metrics counters during processing (requests handled, errors, etc.)
// 3. WITHOUT view types, this requires ugly workarounds or restructuring
//
// THE SOLUTION:
// View types let you call counter-updating methods while iterating!
//
// THEOREMS VERIFIED:
// - Theorem 7: different_fields_no_conflict (counters vs data)
// - Theorem 12: simultaneous_disjoint_field_borrow_safety
// - This is the canonical motivating pattern for view types

// =============================================================================
// HTTP Service: Processes requests and tracks metrics
// =============================================================================

#[derive(Clone, Debug)]
struct Request {
    id: usize,
    path: String,
    processed: bool,
}

struct HttpService {
    // Data being processed
    active_requests: Vec<Request>,
    response_queue: Vec<String>,

    // Metrics (disjoint from data!)
    total_requests_handled: usize,
    total_errors: usize,
    total_successes: usize,
    current_request_id: usize,
}

impl HttpService {
    fn new() -> Self {
        HttpService {
            active_requests: Vec::new(),
            response_queue: Vec::new(),
            total_requests_handled: 0,
            total_errors: 0,
            total_successes: 0,
            current_request_id: 0,
        }
    }

    // =============================================================================
    // METRICS METHODS: Only touch counter fields
    // =============================================================================

    // VIEW TYPE: Only accesses total_requests_handled
    fn record_request_handled(&{mut total_requests_handled} mut self) -> usize {
        self.total_requests_handled += 1;
        self.total_requests_handled
    }

    // VIEW TYPE: Only accesses total_errors
    fn record_error(&{mut total_errors} mut self) {
        self.total_errors += 1;
    }

    // VIEW TYPE: Only accesses total_successes
    fn record_success(&{mut total_successes} mut self) {
        self.total_successes += 1;
    }

    // VIEW TYPE: Only accesses current_request_id
    fn next_request_id(&{mut current_request_id} mut self) -> usize {
        let id = self.current_request_id;
        self.current_request_id += 1;
        id
    }

    // Multi-field view: can update multiple counters
    fn record_outcome(&{mut total_successes, mut total_errors} mut self, success: bool) {
        if success {
            self.total_successes += 1;
        } else {
            self.total_errors += 1;
        }
    }

    // =============================================================================
    // REQUEST PROCESSING: The pattern that requires view types
    // =============================================================================

    fn process_requests(&mut self) {
        // WITHOUT view types: This would fail!
        // WITH view types: Works perfectly!
        for request in &mut self.active_requests {
            // Generate unique ID while iterating
            let req_id = self.next_request_id(); // ✅ WORKS!
            request.id = req_id;

            // Update metrics while iterating
            let count = self.record_request_handled(); // ✅ WORKS!

            // Simulate processing
            let success = request.path.starts_with("/api");
            request.processed = true;

            // Record outcome
            if success {
                self.record_success(); // ✅ WORKS!
            } else {
                self.record_error(); // ✅ WORKS!
            }

            println!("Processed request #{}: {} (total: {})", req_id, request.path, count);
        }
    }

    fn process_responses(&mut self) {
        for response in &mut self.response_queue {
            let count = self.record_request_handled(); // ✅ Different field!
            *response = format!("Response #{}", count);
        }
    }

    // =============================================================================
    // COMPLEX SCENARIO: Multiple metrics updated in one pass
    // =============================================================================

    fn process_with_detailed_metrics(&mut self) {
        for request in &mut self.active_requests {
            // Update THREE different counters during one iteration
            let id = self.next_request_id();
            let total = self.record_request_handled();

            request.id = id;

            let success = request.path != "/error";
            self.record_outcome(success); // Multi-field view spec!

            println!("Request {}: handled as #{}", id, total);
        }
    }
}

// =============================================================================
// DATABASE CONNECTION POOL: Another common pattern
// =============================================================================

struct ConnectionPool {
    connections: Vec<Connection>,
    active_count: usize,
    total_queries_executed: usize,
    failed_queries: usize,
}

#[derive(Clone)]
struct Connection {
    id: usize,
    query_count: usize,
    is_active: bool,
}

impl ConnectionPool {
    fn increment_active(&{mut active_count} mut self) {
        self.active_count += 1;
    }

    fn record_query(&{mut total_queries_executed} mut self) -> usize {
        self.total_queries_executed += 1;
        self.total_queries_executed
    }

    fn record_failure(&{mut failed_queries} mut self) {
        self.failed_queries += 1;
    }

    fn execute_on_all_connections(&mut self) {
        for conn in &mut self.connections {
            if conn.is_active {
                let query_num = self.record_query(); // ✅ WORKS!
                conn.query_count += 1;

                if conn.query_count % 10 == 0 {
                    self.record_failure(); // ✅ Different field!
                }

                self.increment_active(); // ✅ Another field!

                println!("Connection {} executed query #{}", conn.id, query_num);
            }
        }
    }
}

// =============================================================================
// WORKER POOL: Job processing with statistics
// =============================================================================

struct WorkerPool {
    workers: Vec<Worker>,
    jobs_completed: usize,
    jobs_failed: usize,
    total_processing_time_ms: usize,
}

#[derive(Clone)]
struct Worker {
    id: usize,
    jobs_processed: usize,
    is_busy: bool,
}

impl WorkerPool {
    fn record_completion(&{mut jobs_completed, mut total_processing_time_ms} mut self, time_ms: usize) {
        self.jobs_completed += 1;
        self.total_processing_time_ms += time_ms;
    }

    fn record_failure(&{mut jobs_failed} mut self) {
        self.jobs_failed += 1;
    }

    fn assign_jobs(&mut self, job_count: usize) {
        for worker in &mut self.workers {
            if !worker.is_busy && job_count > 0 {
                worker.is_busy = true;
                worker.jobs_processed += 1;

                // Record metrics during iteration
                let time = worker.id * 10; // Simulate processing time
                self.record_completion(time); // ✅ Multi-field view!

                if worker.id % 5 == 0 {
                    self.record_failure(); // ✅ Different field!
                }
            }
        }
    }
}

// =============================================================================
// MAIN: Demonstrate all patterns work
// =============================================================================

fn main() {
    println!("=== Production Metrics Pattern Test ===\n");

    // Test 1: HTTP Service
    let mut service = HttpService::new();
    service.active_requests = vec![
        Request { id: 0, path: "/api/users".to_string(), processed: false },
        Request { id: 0, path: "/api/posts".to_string(), processed: false },
        Request { id: 0, path: "/error".to_string(), processed: false },
        Request { id: 0, path: "/api/health".to_string(), processed: false },
    ];

    println!("Processing requests with metrics...");
    service.process_requests();
    println!("✓ Processed {} requests", service.total_requests_handled);
    println!("✓ Successes: {}, Errors: {}", service.total_successes, service.total_errors);
    assert_eq!(service.total_requests_handled, 4);
    assert_eq!(service.total_successes, 3);
    assert_eq!(service.total_errors, 1);

    // Test 2: Connection Pool
    let mut pool = ConnectionPool {
        connections: vec![
            Connection { id: 1, query_count: 0, is_active: true },
            Connection { id: 2, query_count: 0, is_active: true },
            Connection { id: 3, query_count: 0, is_active: true },
        ],
        active_count: 0,
        total_queries_executed: 0,
        failed_queries: 0,
    };

    println!("\nExecuting queries on connection pool...");
    pool.execute_on_all_connections();
    println!("✓ Total queries: {}", pool.total_queries_executed);
    assert_eq!(pool.total_queries_executed, 3);

    // Test 3: Worker Pool
    let mut workers = WorkerPool {
        workers: vec![
            Worker { id: 1, jobs_processed: 0, is_busy: false },
            Worker { id: 2, jobs_processed: 0, is_busy: false },
            Worker { id: 5, jobs_processed: 0, is_busy: false },
            Worker { id: 10, jobs_processed: 0, is_busy: false },
        ],
        jobs_completed: 0,
        jobs_failed: 0,
        total_processing_time_ms: 0,
    };

    println!("\nAssigning jobs to worker pool...");
    workers.assign_jobs(10);
    println!("✓ Jobs completed: {}", workers.jobs_completed);
    println!("✓ Jobs failed: {}", workers.jobs_failed);
    println!("✓ Total processing time: {}ms", workers.total_processing_time_ms);

    println!("\n=== ALL PRODUCTION PATTERNS WORK ===");
    println!("✓ HTTP service with metrics: WORKS");
    println!("✓ Database connection pool: WORKS");
    println!("✓ Worker pool with stats: WORKS");
    println!("✓ Counter updates during iteration: WORKS");
    println!("✓ Multi-field metrics updates: WORKS");
    println!("✓ This is ESSENTIAL for production systems!");
}
