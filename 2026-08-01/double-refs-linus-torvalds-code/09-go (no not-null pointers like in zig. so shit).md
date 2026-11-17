```go
package main

import "fmt"

type Node struct {
	Value int
	Next  *Node
}

// Implementation 1: Slow (Traditional prev pointer)
func removeEntrySlow(head **Node, entry *Node) {
	var prev *Node = nil
	walk := *head

	for walk != entry && walk != nil {
		prev = walk
		walk = walk.Next
	}

	if prev == nil {
		// Entry was the head
		*head = entry.Next
	} else {
		// Entry was in the middle or end
		prev.Next = entry.Next
	}
}

// Implementation 2: Fast (Indirect Pointer approach)
// This is the Go version of the Linus Torvalds approach.
func removeEntryFast(head **Node, entry *Node) {
	// p is a pointer to a pointer (**Node)
	p := head

	// Iterate until the pointer we are looking at points to the entry
	for *p != entry {
		// Advance p to point to the address of the 'Next' field
		// of the current node.
		p = &((*p).Next)
	}

	// Update the pointer (either the head or a Next field)
	// to skip the entry.
	*p = entry.Next
}

// Helper: O(1) Append using indirect tail pointer
func appendNode(tail **Node, val int) **Node {
	newNode := &Node{Value: val, Next: nil}
	*tail = newNode
	// Return the address of the Next field of the new node
	return &newNode.Next
}

func printList(head *Node) {
	for curr := head; curr != nil; curr = curr.Next {
		fmt.Printf("%d -> ", curr.Value)
	}
	fmt.Println("nil")
}

func main() {
	var head *Node = nil
	// tailPtr points to the pointer that needs to be updated
	tailPtr := &head

	// O(1) Appends
	tailPtr = appendNode(tailPtr, 10)
	tailPtr = appendNode(tailPtr, 20)
	tailPtr = appendNode(tailPtr, 30)
	tailPtr = appendNode(tailPtr, 40)
	tailPtr = appendNode(tailPtr, 50)

	fmt.Println("Original list:")
	printList(head)

	// 1. Remove FRONT (10)
	if head != nil {
		front := head
		removeEntryFast(&head, front)
		fmt.Println("\nAfter removing FRONT (10):")
		printList(head)
	}

	// 2. Remove END (50)
	var end *Node = head
	for end.Next != nil {
		end = end.Next
	}
	removeEntryFast(&head, end)
	fmt.Println("\nAfter removing END (50):")
	printList(head)
}
```
