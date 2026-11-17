| Requirement | Nim Syntax | Explanation |
| :--- | :--- | :--- |
| **Outer Non-Null, Inner Nullable** | `ptr (ptr NodeObj) not nil` | A valid address of a variable that holds a nullable pointer. |
| **Outer Non-Null, Inner Non-Null** | `ptr (ptr NodeObj not nil) not nil` | A valid address of a variable that **must** hold a valid address. |
| **Triple Optionality (`?*?*?int`)** | `ptr ptr Option[int]` | Everything is nullable by default. |

```nim
{.experimental: "strictNotNil".}

type
  NodeObj = object
    value: int
    next: ptr NodeObj
  Node = ptr NodeObj

# --- CONFIGURATION ---
const useFast = true
const modeString = if useFast: 
  "FAST (Indirect Pointer)" else: "SLOW (Prev Pointer)"

## Implementation 1: Slow
proc removeEntrySlow(head: ptr Node not nil, entry: Node not nil) =
  var prev: Node = nil
  var walk = head[]

  while walk != nil and walk != entry:
    prev = walk
    walk = walk.next

  if prev == nil:
    head[] = entry.next
  else:
    prev.next = entry.next

## Implementation 2: Fast (Indirect Pointer approach)
## head is a 'ptr Node' (pointer to a pointer)
proc removeEntryFast(head: ptr Node, entry: Node not nil) =
  # 'p' is our indirect pointer
  var p: ptr Node = head

  # While the pointer stored at address 'p' does not point to 'entry'
  while p[] != entry:
    # addr() takes the address of the field
    # p[] dereferences to get the current node
    p = addr(p[].next)

  # Update the slot (head or a next field) to skip entry
  p[] = entry.next

proc removeEntry(head: ptr Node, entry: Node not nil) =
  when useFast:
    removeEntryFast(head, entry)
  else:
    removeEntrySlow(head, entry)

## Helper: O(1) Append
proc append(tail: ptr Node, val: int): ptr Node =
  # create() is Nim's version of malloc
  let newNode = create(NodeObj)
  newNode.value = val
  newNode.next = nil

  tail[] = newNode
  return addr(newNode.next)

proc printList(head: Node) =
  var curr = head
  while curr != nil:
    stdout.write($curr.value & " -> ")
    curr = curr.next
  echo "nil"

proc main() =
  echo "=== Running with: ", modeString, " ===\n"

  var head: Node = nil
  var tailPtr: ptr Node = addr(head)

  # O(1) Appends
  tailPtr = append(tailPtr, 10)
  tailPtr = append(tailPtr, 20)
  tailPtr = append(tailPtr, 30)
  tailPtr = append(tailPtr, 40)
  tailPtr = append(tailPtr, 50)

  echo "Original list:"
  printList(head)

  # 1. Remove FRONT (10)
  if head != nil:
    let front = head
    removeEntry(addr(head), front)
    dealloc(front) # dealloc() is Nim's free
    echo "\nAfter removing FRONT (10):"
    printList(head)

  # 2. Remove END (50)
  var endNode = head
  while endNode != nil and endNode.next != nil:
    endNode = endNode.next
  
  if endNode != nil:
    removeEntry(addr(head), endNode)
    dealloc(endNode)
    echo "\nAfter removing END (50):"
    printList(head)

  # Cleanup
  var curr = head
  while curr != nil:
    let next = curr.next
    dealloc(curr)
    curr = next

main()
```
