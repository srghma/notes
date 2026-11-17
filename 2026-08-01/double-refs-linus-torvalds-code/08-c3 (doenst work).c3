module main;

import std::io;

struct Node {
    int value;
    Node* next;
}

const bool USE_FAST = true;

/**
 * Implementation 1: Slow
 */
fn void remove_entry_slow(Node** head, Node* entry) {
    Node* prev = null;
    Node* walk = *head;

    while (walk != entry) {
        prev = walk;
        walk = walk.next;
    }

    if (prev == null) {
        *head = entry.next;
    } else {
        prev.next = entry.next;
    }
}

/**
 * Implementation 2: Fast (Indirect Pointer)
 */
fn void remove_entry_fast(Node** head, Node* entry) {
    Node** p = head;

    while (*p != entry) {
        // p points to the previous node's 'next' field (or 'head')
        // we take the address of the current node's 'next' field
        p = &((*p).next);
    }

    // This updates the actual memory slot 'p' points to
    *p = entry.next;
}

fn void remove_entry(Node** head, Node* entry) {
    if (USE_FAST) {
        remove_entry_fast(head, entry);
    } else {
        remove_entry_slow(head, entry);
    }
}

/**
 * O(1) Append
 * Note: mem::new(Node) is the standard C3 allocation syntax
 */
fn Node** append(Node** tail, int val) {
    Node* new_node = mem::new(Node);
    new_node.value = val;
    new_node.next = null;

    *tail = new_node;
    return &new_node.next;
}

fn void print_list(Node* head) {
    Node* curr = head;
    while (curr != null) {
        io::printf("%d -> ", curr.value);
        curr = curr.next;
    }
    io::printn("null");
}

fn int main() {
    io::printf("=== Running with: %s ===\n", USE_FAST ? "FAST" : "SLOW");

    Node* head = null;
    Node** tail_ptr = &head;

    // O(1) Appends
    tail_ptr = append(tail_ptr, 10);
    tail_ptr = append(tail_ptr, 20);
    tail_ptr = append(tail_ptr, 30);
    tail_ptr = append(tail_ptr, 40);
    tail_ptr = append(tail_ptr, 50);

    io::printn("Original list:");
    print_list(head);

    // 1. Remove FRONT (10)
    if (head != null) {
        Node* front = head;
        remove_entry(&head, front);
        mem::free(front);
        io::printn("\nAfter removing FRONT (10):");
        print_list(head);
    }

    // 2. Remove END (50)
    Node* end_search = head;
    while (end_search != null && end_search.next != null) {
        end_search = end_search.next;
    }

    if (end_search != null) {
        remove_entry(&head, end_search);
        mem::free(end_search);
        io::printn("\nAfter removing END (50):");
        print_list(head);
    }

    // Cleanup remaining memory
    Node* curr = head;
    while (curr != null) {
        Node* next = curr.next;
        mem::free(curr);
        curr = next;
    }

    return 0;
}
