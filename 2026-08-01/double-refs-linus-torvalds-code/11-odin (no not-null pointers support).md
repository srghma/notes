```odin
package main

import "core:fmt"

Node :: struct {
	value: i32,
	next:  ^Node,
}

// --- CONFIGURATION ---
USE_FAST :: true
MODE_STRING := USE_FAST ? "FAST (Indirect Pointer)" : "SLOW (Prev Pointer)"

/**
 * Implementation 1: Slow (Tracking previous node)
 */
remove_entry_slow :: proc(head: ^^Node, entry: ^Node) {
	// Assertions enforce our "Must not be null" contract
	assert(head != nil, "head handle must not be nil")
	assert(entry != nil, "entry node must not be nil")

	prev: ^Node = nil
	walk := head^

	for walk != entry && walk != nil {
		prev = walk
		walk = walk.next
	}

	if prev == nil {
		head^ = entry.next
	} else {
		prev.next = entry.next
	}
}

/**
 * Implementation 2: Fast (Indirect Pointer approach)
 * This is the Odin version of the Linus Torvalds approach.
 */
remove_entry_fast :: proc(head: ^^Node, entry: ^Node) {
	// Assertions enforce our "Must not be null" contract
	assert(head != nil, "head handle must not be nil")
	assert(entry != nil, "entry node must not be nil")

	p := head

	// Traverse until the pointer in slot 'p' points to entry
	for p^ != entry {
		// p points to the previous node's 'next' field (or the head)
		// We move p to point to the current node's 'next' field
		p = &p^.next
	}

	// Update the memory slot (head or a next field) to skip the entry
	p^ = entry.next
}

/**
 * Dispatcher
 * 'when' is Odin's version of 'if constexpr'
 */
remove_entry :: proc(head: ^^Node, entry: ^Node) {
	when USE_FAST {
		remove_entry_fast(head, entry)
	} else {
		remove_entry_slow(head, entry)
	}
}

/**
 * Helper: O(1) Append using indirect tail pointer
 */
append :: proc(tail: ^^Node, val: i32) -> ^^Node {
	assert(tail != nil)

	new_node := new(Node)
	new_node.value = val
	new_node.next = nil

	tail^ = new_node
	return &new_node.next
}

print_list :: proc(head: ^Node) {
	for curr := head; curr != nil; curr = curr.next {
		fmt.printf("%d -> ", curr.value)
	}
	fmt.println("nil")
}

main :: proc() {
	fmt.printf("=== Running with: %s ===\n\n", MODE_STRING)

	head: ^Node = nil
	tail_ptr := &head

	// O(1) Appends
	tail_ptr = append(tail_ptr, 10)
	tail_ptr = append(tail_ptr, 20)
	tail_ptr = append(tail_ptr, 30)
	tail_ptr = append(tail_ptr, 40)
	tail_ptr = append(tail_ptr, 50)

	fmt.println("Original list:")
	print_list(head)

	// 1. Remove FRONT (10)
	if head != nil {
		front := head
		remove_entry(&head, front)
		free(front)
		fmt.println("\nAfter removing FRONT (10):")
		print_list(head)
	}

	// 2. Remove END (50)
	// First, find the end node
	end_search := head
	for end_search != nil && end_search.next != nil {
		end_search = end_search.next
	}

	if end_search != nil {
		remove_entry(&head, end_search)
		free(end_search)
		fmt.println("\nAfter removing END (50):")
		print_list(head)
	}

	// Cleanup remaining memory
	curr := head
	for curr != nil {
		next := curr.next
		free(curr)
		curr = next
	}
}
```
