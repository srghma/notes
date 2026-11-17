const std = @import("std");

const Node = struct {
    value: i32 = 0,
    next: ?*Node = null,
};

// --- CONFIGURATION ---
const use_fast = true;
const mode_string = if (use_fast) "FAST (Indirect Pointer)" else "SLOW (Prev Pointer)";

/// Implementation 1: Slow (Tracking previous node)
fn removeEntrySlow(head: *?*Node, entry: *Node) void { // non-null pointer to nullable pointer to non-optional Node. Why to nullable? Bc we will make the stack cell 00000 if only one node
    var prev: ?*Node = null;
    var walk = head.*;

    while (walk != entry) {
        prev = walk;
        // .? asserts walk is not null because we assume the entry exists in the list
        walk = walk.?.next;
    }

    if (prev == null) {
        head.* = entry.next;
    } else {
        prev.?.next = entry.next;
    }
}

/// Implementation 2: Fast (Using indirect pointers)
/// This is the Zig version of the "Linus Torvalds" pointer approach
fn removeEntryFast(head: *?*Node, entry: *Node) void {
    // p is a pointer to a pointer (indirect pointer)
    var p: *?*Node = head;

    // While the pointer we are looking at doesn't point to the target entry
    while (p.* != entry) {
        // Move 'p' to point to the address of the 'next' field of the current node
        p = &p.*.?.next;
    }

    // Direct assignment: update the 'next' field of the previous node
    // (or the head itself) to skip the entry.
    p.* = entry.next;
}

inline fn removeEntry(head: *?*Node, entry: *Node) void {
    if (comptime use_fast) {
        removeEntryFast(head, entry);
    } else {
        removeEntrySlow(head, entry);
    }
}

/// Helper: Print the list
fn printList(head: ?*Node) void {
    var curr = head;
    while (curr) |n| {
        std.debug.print("{} -> ", .{n.value});
        curr = n.next;
    }
    std.debug.print("null\n", .{});
}

/// Helper: O(1) Append using indirect tail pointer
/// Returns the address of the 'next' field of the new node
fn append(tail: *?*Node, allocator: std.mem.Allocator, val: i32) !*?*Node {
    const new_node = try allocator.create(Node);
    new_node.* = .{ .value = val, .next = null };

    tail.* = new_node;
    return &new_node.next;
}

pub fn main() !void {
    // page_allocator is the most stable allocator across different Zig versions
    const allocator = std.heap.page_allocator;

    std.debug.print("=== Running with: {s} ===\n\n", .{mode_string});

    var head: ?*Node = null;
    var tail_ptr: *?*Node = &head;

    // O(1) Appends (Zero loops, Zero 'if' statements)
    tail_ptr = try append(tail_ptr, allocator, 10);
    tail_ptr = try append(tail_ptr, allocator, 20);
    tail_ptr = try append(tail_ptr, allocator, 30);
    tail_ptr = try append(tail_ptr, allocator, 40);
    tail_ptr = try append(tail_ptr, allocator, 50);

    std.debug.print("Original list:\n", .{});
    printList(head);

    // 1. Remove FRONT (10)
    if (head) |front| {
        removeEntry(&head, front);
        allocator.destroy(front);
        std.debug.print("\nAfter removing FRONT (10):\n", .{});
        printList(head);
    }

    // 2. Remove END (50)
    var end_search = head;
    while (end_search) |n| {
        if (n.next == null) break;
        end_search = n.next;
    }

    if (end_search) |end| {
        removeEntry(&head, end);
        allocator.destroy(end);
        std.debug.print("\nAfter removing END (50):\n", .{});
        printList(head);
    }

    // Cleanup remaining list memory
    var curr = head;
    while (curr) |n| {
        const next = n.next;
        allocator.destroy(n);
        curr = next;
    }
}
