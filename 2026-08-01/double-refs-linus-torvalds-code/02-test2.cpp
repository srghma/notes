#include <iostream>
#include <string_view>

struct node {
  int value{0};        // Fix S836: Default initialization prevents garbage values
  node *next{nullptr};  // Fix S836: Default initialization prevents garbage values
};

// --- CONFIGURATION SWITCH ---
// Fix S5028: Replaced #define with constexpr
constexpr bool USE_FAST = true;

// Implementation 1: Slow
void remove_list_entry_slow(node **head, node *entry) {
  node *prev = nullptr; // Fix S1659: Dedicated statement for each identifier
  node *walk = *head;   // Fix S1659: Dedicated statement for each identifier

  while (walk != entry) {
    prev = walk;
    walk = walk->next;
  }
  if (!prev)
    *head = entry->next;
  else
    prev->next = entry->next;
}

// Implementation 2: Fast
void remove_list_entry_fast(node **head, node *entry) {
  node **p = head;
  while (*p != entry)
    p = &(*p)->next;
  *p = entry->next;
}

// Fix S5028: Replaced macro selection with constexpr string and if constexpr
constexpr std::string_view MODE_STRING = USE_FAST ? "FAST (Indirect Pointer)" : "SLOW (Prev Pointer)";

inline void remove_list_entry(node **head, node *entry) {
  if constexpr (USE_FAST) {
    remove_list_entry_fast(head, entry);
  } else {
    remove_list_entry_slow(head, entry);
  }
}

// Helper: Print the list
void print_list(const node *head) {
  for (const node *curr = head; curr != nullptr; curr = curr->next) {
    std::cout << curr->value << " -> ";
  }
  std::cout << "nullptr\n";
}

// Helper: Append to list in O(1) time (Zero loops, Zero 'if' statements)
void append(node **&tail, int val) {
  auto *new_node = new node{val, nullptr}; // NOSONAR (cpp:S5025) - Intentional raw heap allocation
  *tail = new_node;       // Link new node into the list
  tail = &new_node->next; // Move tail pointer to point to the new node's 'next' field
}

int main() {
  std::cout << "=== Running with: " << MODE_STRING << " ===\n\n";

  node *head = nullptr;
  node **tail = &head; // 'tail' points to where the next node should be inserted

  // All appends are now O(1) instantaneous calls!
  append(tail, 10);
  append(tail, 20);
  append(tail, 30);
  append(tail, 40);
  append(tail, 50);

  std::cout << "Original list:\n";
  print_list(head);

  // 1. Remove FRONT
  node *front = head;
  remove_list_entry(&head, front);
  delete front; // NOSONAR (cpp:S5025) - Intentional manual memory management

  std::cout << "\nAfter removing FRONT (10):\n";
  print_list(head);

  // 2. Remove END
  node *end = head;
  while (end->next != nullptr) {
    end = end->next;
  }
  remove_list_entry(&head, end);
  delete end; // NOSONAR (cpp:S5025) - Intentional manual memory management

  std::cout << "\nAfter removing END (50):\n";
  print_list(head);

  // Clean remaining list memory
  while (head != nullptr) {
    node *temp = head;
    head = head->next;
    delete temp; // NOSONAR (cpp:S5025) - Intentional cleanup
  }

  return 0;
}
