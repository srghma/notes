```cpp
// The Object (a struct)
static const lean_string_object l_foo_value = { ... };

// The Function (expects a pointer)
void lean_inc_ref(lean_object * o);

// Scenario A: Correct
// You might notice something strange. foo is a lean_string_object, but the function takes a lean_object *. Why does that work?
// Lean uses a clever trick called Header Compatibility
lean_inc_ref((lean_object*)&l_foo_value); // Passing the address - OK

// Scenario B: Incorrect
lean_inc_ref(l_foo_value); // ERROR!
```

```cpp
#include <iostream>

// 1. The "Base Class" (The Header)
struct lean_object {
    size_t m_rc;      // Ref count: 0 = immortal, 1 = exclusive, >1 = shared
    int m_tag;        // 249 for String, etc.
};

// 2. The "Derived Class" (The String)
struct lean_string_object {
    lean_object m_header; // Header MUST be first for the pointer trick to work
    int m_size;
    const char* m_data;
};

// 3. The Function (Expects a POINTER to the header)
void lean_inc_ref(lean_object* o) {
    std::cout << "Checking refcount at address: " << o << std::endl;

    if (o->m_rc == 0) {
        std::cout << "  RC is 0: This is a persistent object. Doing nothing.\n" << std::endl;
    } else {
        o->m_rc++;
        std::cout << "  RC incremented to: " << o->m_rc << "\n" << std::endl;
    }
}

// 4. Create the string in .rodata (static const)
static const lean_string_object l_foo_value = {
    {0, 249}, // m_rc = 0 (immortal), m_tag = 249 (String)
    4,        // size
    "foo"     // data
};

int main() {
    // --- SCENARIO A: The Correct Way (Passing the Address) ---
    // We take the address of our struct (&) and cast it to a generic object pointer
    std::cout << "Calling with pointer:" << std::endl;
    lean_inc_ref((lean_object*)&l_foo_value);

    // --- SCENARIO B: The Incorrect Way (Passing the Value) ---
    // UNCOMMENT the line below to see the compiler error:
    // lean_inc_ref(l_foo_value);

    /*
       Why Scenario B fails:
       Error: cannot convert 'lean_string_object' to 'lean_object*'

       Reason: A 'house' (the struct) cannot fit into an 'envelope' (the pointer).
       The function wants a 64-bit address, not 32 bytes of raw data.
    */

    // --- SCENARIO C: A Heap Object (rc > 0) ---
    std::cout << "Calling with a heap object (rc=1):" << std::endl;
    lean_object* heap_obj = new lean_object{1, 249};
    lean_inc_ref(heap_obj);

    delete heap_obj;
    return 0;
}
```
