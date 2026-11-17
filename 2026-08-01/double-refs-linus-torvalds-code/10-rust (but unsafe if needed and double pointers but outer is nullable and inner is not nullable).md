```rust
use std::ptr::{NonNull};

struct Node {
    value: i32,
    // The "inner" pointer. Using Option<NonNull> is the Rust way to
    // have a "nullable pointer" that is non-nullable when active.
    next: Option<NonNull<Node>>,
}

// HERE IS A PROBLEM : I WANT TO REQUIRE THAT head ON INPUT is NOT NULL, but on output MAY BE NULL, and the memory location should be same
unsafe fn remove_entry_fast(head: &mut Option<NonNull<Node>>, entry: NonNull<Node>) {
    // 1. Handle "outer is nullable" check
    // THIS IS NEEDED WHEN USING
    // head: *mut Option<NonNull<Node>>
    // instead of
    // head: &mut Option<NonNull<Node>>
    // NOT NEEDED NOT bc & guarantees NonNull pointers
    //if head.is_null() { return; }

    // 'p' is our indirect pointer (pointer to a pointer)
    let mut p: *mut Option<NonNull<Node>> = head;

    // While the pointer at 'p' does not point to our entry
    // We compare the addresses of the NonNull pointers
    unsafe {
    while (*p).is_some_and(|node_ptr| node_ptr != entry) {
        // Move 'p' to point to the address of the 'next' field of the current node
        // We unwrap the optional because the while loop condition guaranteed it exists
        p = &mut (*(*p).unwrap().as_ptr()).next;
    }

    // Direct assignment: The pointer at 'p' (either 'head' or a 'next' field)
    // is updated to point to whatever the entry was pointing to.
    *p = (*entry.as_ptr()).next;
    }
}

// TODO: maybe this will reuse

/// The "Linus" signature:
/// - head_addr: A Non-nullable pointer to a nullable pointer slot.
/// - entry: The non-nullable node to remove.
/// - Returns: A reference to the same memory slot after modification.
// unsafe fn remove_entry_fast<'a>(
//     head_addr: NonNull<Option<NonNull<Node>>>,
//     entry: NonNull<Node>
// ) -> &'a Option<NonNull<Node>> {
//
//     // p is our indirect pointer (starts at the address of 'head')
//     let mut p: *mut Option<NonNull<Node>> = head_addr.as_ptr();
//
//     unsafe {
//         // While the pointer inside slot 'p' does not point to 'entry'
//         while (*p).map_or(false, |node_ptr| node_ptr != entry) {
//             // p = address of the 'next' field of the current node
//             p = &mut (*(*p).unwrap().as_ptr()).next;
//         }
//
//         // The "Magic" update: Write the successor's address into the slot 'p' points to.
//         // This slot is either the 'head' variable or a 'next' field.
//         *p = (*entry.as_ptr()).next;
//
//         // Return a reference to the updated memory location
//         &*p
//     }
// }


/// Helper: O(1) Append using indirect tail pointer
unsafe fn append(tail: *mut Option<NonNull<Node>>, val: i32) -> *mut Option<NonNull<Node>> {
    // Allocate a new node on the heap (Box::into_raw keeps it alive)
    let new_node = Box::into_raw(Box::new(Node {
        value: val,
        next: None,
    }));

    unsafe {
    let non_null_node = NonNull::new_unchecked(new_node);

    // Link the new node into the slot pointed to by tail
    *tail = Some(non_null_node);

    // Return the address of the new node's next field
    &mut (*new_node).next
    }
}

fn print_list(head: Option<NonNull<Node>>) {
    let mut curr = head;
    while let Some(node_ptr) = curr {
        unsafe {
            print!("{} -> ", (*node_ptr.as_ptr()).value);
            curr = (*node_ptr.as_ptr()).next;
        }
    }
    println!("null");
}

#[inline(never)]
pub fn main() {
    let mut head: Option<NonNull<Node>> = None;
    let mut tail_ptr: *mut Option<NonNull<Node>> = &mut head;

    unsafe {
        // O(1) Appends
        tail_ptr = append(tail_ptr, 10);
        tail_ptr = append(tail_ptr, 20);
        tail_ptr = append(tail_ptr, 30);
        tail_ptr = append(tail_ptr, 40);
        _ = append(tail_ptr, 50); // Use _ to avoid unused assignment warning

        println!("Original list:");
        print_list(head);

        // 1. Remove FRONT (10)
        if let Some(front) = head {
            remove_entry_fast(&mut head, front);
            // Re-constitute Box to free memory
            let _ = Box::from_raw(front.as_ptr());
            println!("\nAfter removing FRONT (10):");
            print_list(head);
        }

        // 2. Remove END (50)
        let mut end = head.unwrap();
        while let Some(next_node) = (*end.as_ptr()).next {
            end = next_node;
        }
        remove_entry_fast(&mut head, end);
        let _ = Box::from_raw(end.as_ptr());
        println!("\nAfter removing END (50):");
        print_list(head);

        // Cleanup remaining
        let mut curr = head;
        while let Some(node_ptr) = curr {
            let next = (*node_ptr.as_ptr()).next;
            let _ = Box::from_raw(node_ptr.as_ptr());
            curr = next;
        }
    }
}
```
