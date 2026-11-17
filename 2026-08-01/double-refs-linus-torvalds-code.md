1. http://felipec.github.io/good-taste/parts/1.html
2. http://felipec.github.io/good-taste/parts/2.html
3. http://felipec.github.io/good-taste/parts/3.html

- BM_initialSlow 6,328.464
- BM_initialFast 6,419.343
- BM_GLib 6,114.761
- BM_Linux 6,019.624

SP (Stack Pointer, highest word), LV (Local Variable pointer), ~~and TOS (Top of Stack)~~, PC program counter
CPP constant pool pointer

https://drive.google.com/drive/folders/1YHLjEdp6AomSQEPJ8z4iXI8VkKz3v3RB

%rbp - register base pointer (start) LV pointer, lowest word of function foo local variables, local variable
$rsp - register stack pointer (end), SP

| **Inner \ Outer** | **Outer Pointer is Non-Nullable (`*...`)** | **Outer Pointer is Nullable (`?*...`)** |
| :--- | :--- | :--- |
| **Inner Pointer is Non-Nullable (`*Node`)** | IF non-optional node THEN **`**Node`** <br> ELSE **`**?Node`** | IF non-optional node THEN **`?**Node`** <br> ELSE **`?**?Node`** |
| **Inner Pointer is Nullable (`?*Node`)** | IF non-optional node THEN **`*?*Node`** (Linus) <br> ELSE **`*?*?Node`** | IF non-optional node THEN **`?*?*Node`** <br> ELSE **`?*?*?Node`** |

```
--- Triple-Nullability Cube (Base: 0x7ffe9e4604b0) ---

V1: outer ptr [null] -> STOP
V2: outer ptr [0x7ffe9e460498 (base-24)] -> inner ptr [null] -> STOP
V3: outer ptr [0x7ffe9e4604a0 (base-16)] -> inner ptr [0x7ffe9e4604b4 (base+4)] -> int was null -> STOP
V4: outer ptr [0x7ffe9e4604a8 (base-8)] -> inner ptr [0x7ffe9e4604bc (base+12)] -> int was 1
```

<!--

-->

- the safe version was fastest https://github.com/srghma/aeneas-test
