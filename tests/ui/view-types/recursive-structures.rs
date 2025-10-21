//@ check-pass
#![feature(view_types)]
#![allow(unused, incomplete_features)]

// RECURSIVE STRUCTURES TEST
//
// This test verifies that view types work correctly with recursive and
// self-referential data structures. These are common patterns in systems
// programming and data structure implementations.
//
// Tested patterns:
// - Binary trees (Box-based recursion)
// - Linked lists
// - N-ary trees
// - Graphs with adjacency lists
// - Structures with parent pointers (Rc/Weak)
// - Arena-allocated trees with indices

use std::rc::{Rc, Weak};
use std::cell::RefCell;

// =============================================================================
// Test 1: Binary Tree with Box
// =============================================================================

#[derive(Debug)]
struct TreeNode {
    value: i32,
    left: Option<Box<TreeNode>>,
    right: Option<Box<TreeNode>>,
}

struct BinaryTree {
    root: Option<Box<TreeNode>>,
    node_count: usize,
    height: usize,
}

impl BinaryTree {
    fn new() -> Self {
        BinaryTree {
            root: None,
            node_count: 0,
            height: 0,
        }
    }

    fn increment_count(&{mut node_count} mut self) {
        self.node_count += 1;
    }

    fn get_count(&{node_count} self) -> usize {
        self.node_count
    }

    fn set_height(&{mut height} mut self, h: usize) {
        self.height = h;
    }

    fn get_height(&{height} self) -> usize {
        self.height
    }

    fn has_root(&{root} self) -> bool {
        self.root.is_some()
    }

    // Can access root while count is separate
    fn count_and_check(&{node_count, root} self) -> (usize, bool) {
        (self.node_count, self.root.is_some())
    }
}

// =============================================================================
// Test 2: Singly Linked List
// =============================================================================

#[derive(Debug)]
struct ListNode {
    value: i32,
    next: Option<Box<ListNode>>,
}

struct LinkedList {
    head: Option<Box<ListNode>>,
    tail_value: Option<i32>,
    length: usize,
}

impl LinkedList {
    fn new() -> Self {
        LinkedList {
            head: None,
            tail_value: None,
            length: 0,
        }
    }

    fn increment_length(&{mut length} mut self) {
        self.length += 1;
    }

    fn get_length(&{length} self) -> usize {
        self.length
    }

    fn set_tail_value(&{mut tail_value} mut self, value: i32) {
        self.tail_value = Some(value);
    }

    fn get_tail_value(&{tail_value} self) -> Option<i32> {
        self.tail_value
    }

    fn is_empty(&{head} self) -> bool {
        self.head.is_none()
    }

    fn stats(&{length, tail_value} self) -> (usize, Option<i32>) {
        (self.length, self.tail_value)
    }
}

// =============================================================================
// Test 3: N-ary Tree (Vec of children)
// =============================================================================

#[derive(Debug)]
struct NAryNode {
    value: String,
    children: Vec<Box<NAryNode>>,
}

struct NAryTree {
    root: Option<Box<NAryNode>>,
    total_nodes: usize,
    max_depth: usize,
}

impl NAryTree {
    fn new() -> Self {
        NAryTree {
            root: None,
            total_nodes: 0,
            max_depth: 0,
        }
    }

    fn add_node(&{mut total_nodes} mut self) {
        self.total_nodes += 1;
    }

    fn node_count(&{total_nodes} self) -> usize {
        self.total_nodes
    }

    fn update_depth(&{mut max_depth} mut self, depth: usize) {
        if depth > self.max_depth {
            self.max_depth = depth;
        }
    }

    fn get_depth(&{max_depth} self) -> usize {
        self.max_depth
    }

    fn has_root(&{root} self) -> bool {
        self.root.is_some()
    }
}

// =============================================================================
// Test 4: Graph with Adjacency List
// =============================================================================

use std::collections::HashMap;

#[derive(Debug, Clone)]
struct GraphNode {
    id: usize,
    data: String,
}

struct Graph {
    nodes: HashMap<usize, GraphNode>,
    edges: HashMap<usize, Vec<usize>>,
    node_count: usize,
    edge_count: usize,
}

impl Graph {
    fn new() -> Self {
        Graph {
            nodes: HashMap::new(),
            edges: HashMap::new(),
            node_count: 0,
            edge_count: 0,
        }
    }

    fn add_node_count(&{mut node_count} mut self) {
        self.node_count += 1;
    }

    fn add_edge_count(&{mut edge_count} mut self) {
        self.edge_count += 1;
    }

    fn get_node(&{nodes} self, id: usize) -> Option<&GraphNode> {
        self.nodes.get(&id)
    }

    fn get_edges(&{edges} self, id: usize) -> Option<&Vec<usize>> {
        self.edges.get(&id)
    }

    fn total_nodes(&{node_count} self) -> usize {
        self.node_count
    }

    fn total_edges(&{edge_count} self) -> usize {
        self.edge_count
    }

    fn stats(&{node_count, edge_count} self) -> (usize, usize) {
        (self.node_count, self.edge_count)
    }
}

// =============================================================================
// Test 5: Tree with Parent Pointers (Rc/Weak)
// =============================================================================

#[derive(Debug)]
struct TreeWithParent {
    value: i32,
    parent: Weak<RefCell<TreeWithParent>>,
    children: Vec<Rc<RefCell<TreeWithParent>>>,
}

struct TreeManager {
    root: Option<Rc<RefCell<TreeWithParent>>>,
    statistics: RefCell<TreeStats>,
}

#[derive(Debug, Default)]
struct TreeStats {
    node_count: usize,
    max_depth: usize,
}

impl TreeManager {
    fn new() -> Self {
        TreeManager {
            root: None,
            statistics: RefCell::new(TreeStats::default()),
        }
    }

    fn increment_node_count(&{statistics} self) {
        self.statistics.borrow_mut().node_count += 1;
    }

    fn get_node_count(&{statistics} self) -> usize {
        self.statistics.borrow().node_count
    }

    fn set_max_depth(&{statistics} self, depth: usize) {
        let mut stats = self.statistics.borrow_mut();
        if depth > stats.max_depth {
            stats.max_depth = depth;
        }
    }

    fn get_max_depth(&{statistics} self) -> usize {
        self.statistics.borrow().max_depth
    }

    fn has_root(&{root} self) -> bool {
        self.root.is_some()
    }

    fn get_stats(&{statistics} self) -> (usize, usize) {
        let stats = self.statistics.borrow();
        (stats.node_count, stats.max_depth)
    }
}

// =============================================================================
// Test 6: Arena-Allocated Tree (Index-based)
// =============================================================================

#[derive(Debug, Clone, Copy, PartialEq)]
struct NodeIndex(usize);

#[derive(Debug)]
struct ArenaNode {
    value: i32,
    parent: Option<NodeIndex>,
    children: Vec<NodeIndex>,
}

struct ArenaTree {
    arena: Vec<ArenaNode>,
    root: Option<NodeIndex>,
    free_list: Vec<NodeIndex>,
}

impl ArenaTree {
    fn new() -> Self {
        ArenaTree {
            arena: Vec::new(),
            root: None,
            free_list: Vec::new(),
        }
    }

    fn allocate(&{mut arena} mut self, value: i32) -> NodeIndex {
        let idx = NodeIndex(self.arena.len());
        self.arena.push(ArenaNode {
            value,
            parent: None,
            children: Vec::new(),
        });
        idx
    }

    fn get_node(&{arena} self, idx: NodeIndex) -> Option<&ArenaNode> {
        self.arena.get(idx.0)
    }

    fn get_node_mut(&{mut arena} mut self, idx: NodeIndex) -> Option<&mut ArenaNode> {
        self.arena.get_mut(idx.0)
    }

    fn set_root(&{mut root} mut self, idx: NodeIndex) {
        self.root = Some(idx);
    }

    fn get_root(&{root} self) -> Option<NodeIndex> {
        self.root
    }

    fn add_to_free_list(&{mut free_list} mut self, idx: NodeIndex) {
        self.free_list.push(idx);
    }

    fn free_count(&{free_list} self) -> usize {
        self.free_list.len()
    }

    fn arena_size(&{arena} self) -> usize {
        self.arena.len()
    }
}

// =============================================================================
// Test 7: Doubly Linked List with Rc/RefCell
// =============================================================================

#[derive(Debug)]
struct DListNode {
    value: i32,
    prev: Option<Weak<RefCell<DListNode>>>,
    next: Option<Rc<RefCell<DListNode>>>,
}

struct DoublyLinkedList {
    head: Option<Rc<RefCell<DListNode>>>,
    tail: Option<Weak<RefCell<DListNode>>>,
    length: usize,
}

impl DoublyLinkedList {
    fn new() -> Self {
        DoublyLinkedList {
            head: None,
            tail: None,
            length: 0,
        }
    }

    fn increment_length(&{mut length} mut self) {
        self.length += 1;
    }

    fn decrement_length(&{mut length} mut self) {
        if self.length > 0 {
            self.length -= 1;
        }
    }

    fn get_length(&{length} self) -> usize {
        self.length
    }

    fn has_head(&{head} self) -> bool {
        self.head.is_some()
    }

    fn has_tail(&{tail} self) -> bool {
        self.tail.is_some()
    }
}

// =============================================================================
// Test 8: Composite Pattern - File System Tree
// =============================================================================

#[derive(Debug)]
enum FSEntry {
    File { name: String, size: usize },
    Directory { name: String, children: Vec<Box<FSEntry>> },
}

struct FileSystem {
    root: Option<Box<FSEntry>>,
    total_files: usize,
    total_dirs: usize,
    total_size: usize,
}

impl FileSystem {
    fn new() -> Self {
        FileSystem {
            root: None,
            total_files: 0,
            total_dirs: 0,
            total_size: 0,
        }
    }

    fn add_file(&{mut total_files} mut self) {
        self.total_files += 1;
    }

    fn add_dir(&{mut total_dirs} mut self) {
        self.total_dirs += 1;
    }

    fn add_size(&{mut total_size} mut self, size: usize) {
        self.total_size += size;
    }

    fn file_count(&{total_files} self) -> usize {
        self.total_files
    }

    fn dir_count(&{total_dirs} self) -> usize {
        self.total_dirs
    }

    fn total_size(&{total_size} self) -> usize {
        self.total_size
    }

    fn has_root(&{root} self) -> bool {
        self.root.is_some()
    }

    fn stats(&{total_files, total_dirs, total_size} self) -> (usize, usize, usize) {
        (self.total_files, self.total_dirs, self.total_size)
    }
}

// =============================================================================
// Test 9: Trie (Prefix Tree)
// =============================================================================

#[derive(Debug)]
struct TrieNode {
    children: HashMap<char, Box<TrieNode>>,
    is_end: bool,
}

struct Trie {
    root: Box<TrieNode>,
    word_count: usize,
    node_count: usize,
}

impl Trie {
    fn new() -> Self {
        Trie {
            root: Box::new(TrieNode {
                children: HashMap::new(),
                is_end: false,
            }),
            word_count: 0,
            node_count: 1,
        }
    }

    fn increment_word_count(&{mut word_count} mut self) {
        self.word_count += 1;
    }

    fn increment_node_count(&{mut node_count} mut self) {
        self.node_count += 1;
    }

    fn get_word_count(&{word_count} self) -> usize {
        self.word_count
    }

    fn get_node_count(&{node_count} self) -> usize {
        self.node_count
    }

    fn counts(&{word_count, node_count} self) -> (usize, usize) {
        (self.word_count, self.node_count)
    }
}

// =============================================================================
// Test 10: Skip List (Multi-level Linked List)
// =============================================================================

#[derive(Debug)]
struct SkipNode {
    value: i32,
    forward: Vec<Option<Box<SkipNode>>>,
}

struct SkipList {
    head: Box<SkipNode>,
    max_level: usize,
    current_level: usize,
    size: usize,
}

impl SkipList {
    fn new(max_level: usize) -> Self {
        SkipList {
            head: Box::new(SkipNode {
                value: i32::MIN,
                forward: (0..max_level).map(|_| None).collect(),
            }),
            max_level,
            current_level: 0,
            size: 0,
        }
    }

    fn increment_size(&{mut size} mut self) {
        self.size += 1;
    }

    fn get_size(&{size} self) -> usize {
        self.size
    }

    fn update_level(&{mut current_level} mut self, level: usize) {
        if level > self.current_level {
            self.current_level = level;
        }
    }

    fn get_current_level(&{current_level} self) -> usize {
        self.current_level
    }

    fn get_max_level(&{max_level} self) -> usize {
        self.max_level
    }
}

// =============================================================================
// Main: Test All Recursive Structures
// =============================================================================

fn main() {
    // Test 1: Binary Tree
    let mut btree = BinaryTree::new();
    btree.increment_count();
    btree.increment_count();
    assert_eq!(btree.get_count(), 2);
    btree.set_height(3);
    assert_eq!(btree.get_height(), 3);
    assert!(!btree.has_root());
    let (count, has_root) = btree.count_and_check();
    assert_eq!(count, 2);
    assert!(!has_root);

    // Test 2: Linked List
    let mut llist = LinkedList::new();
    llist.increment_length();
    llist.increment_length();
    assert_eq!(llist.get_length(), 2);
    llist.set_tail_value(42);
    assert_eq!(llist.get_tail_value(), Some(42));
    assert!(llist.is_empty());
    let (len, tail) = llist.stats();
    assert_eq!(len, 2);
    assert_eq!(tail, Some(42));

    // Test 3: N-ary Tree
    let mut narytree = NAryTree::new();
    narytree.add_node();
    narytree.add_node();
    assert_eq!(narytree.node_count(), 2);
    narytree.update_depth(5);
    assert_eq!(narytree.get_depth(), 5);
    assert!(!narytree.has_root());

    // Test 4: Graph
    let mut graph = Graph::new();
    graph.add_node_count();
    graph.add_edge_count();
    assert_eq!(graph.total_nodes(), 1);
    assert_eq!(graph.total_edges(), 1);
    let (nodes, edges) = graph.stats();
    assert_eq!(nodes, 1);
    assert_eq!(edges, 1);

    // Test 5: Tree with Parent Pointers
    let tree_mgr = TreeManager::new();
    tree_mgr.increment_node_count();
    tree_mgr.increment_node_count();
    assert_eq!(tree_mgr.get_node_count(), 2);
    tree_mgr.set_max_depth(4);
    assert_eq!(tree_mgr.get_max_depth(), 4);
    assert!(!tree_mgr.has_root());
    let (nodes, depth) = tree_mgr.get_stats();
    assert_eq!(nodes, 2);
    assert_eq!(depth, 4);

    // Test 6: Arena Tree
    let mut arena = ArenaTree::new();
    let node1 = arena.allocate(10);
    let node2 = arena.allocate(20);
    arena.set_root(node1);
    assert_eq!(arena.get_root(), Some(node1));
    assert_eq!(arena.arena_size(), 2);
    arena.add_to_free_list(node2);
    assert_eq!(arena.free_count(), 1);

    // Test 7: Doubly Linked List
    let mut dlist = DoublyLinkedList::new();
    dlist.increment_length();
    assert_eq!(dlist.get_length(), 1);
    dlist.decrement_length();
    assert_eq!(dlist.get_length(), 0);
    assert!(!dlist.has_head());
    assert!(!dlist.has_tail());

    // Test 8: File System
    let mut fs = FileSystem::new();
    fs.add_file();
    fs.add_dir();
    fs.add_size(1024);
    assert_eq!(fs.file_count(), 1);
    assert_eq!(fs.dir_count(), 1);
    assert_eq!(fs.total_size(), 1024);
    let (files, dirs, size) = fs.stats();
    assert_eq!(files, 1);
    assert_eq!(dirs, 1);
    assert_eq!(size, 1024);

    // Test 9: Trie
    let mut trie = Trie::new();
    trie.increment_word_count();
    trie.increment_node_count();
    assert_eq!(trie.get_word_count(), 1);
    assert_eq!(trie.get_node_count(), 2);
    let (words, nodes) = trie.counts();
    assert_eq!(words, 1);
    assert_eq!(nodes, 2);

    // Test 10: Skip List
    let mut slist = SkipList::new(4);
    slist.increment_size();
    assert_eq!(slist.get_size(), 1);
    slist.update_level(2);
    assert_eq!(slist.get_current_level(), 2);
    assert_eq!(slist.get_max_level(), 4);

    println!("✓ All recursive structure tests passed!");
}
