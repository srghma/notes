const std = @import("std");

inline fn deepPrint(outer: ?*?*?i32, base_addr: usize) void {
    // Helper to print formatting logic once
    const printAddr = struct {
        fn run(label: []const u8, ptr: anytype, base: usize) void {
            const addr = @intFromPtr(ptr);
            const offset = @as(i128, @intCast(addr)) - @as(i128, @intCast(base));
            // Manually add '+' for positive offsets since Zig doesn't support {:+}
            const sign = if (offset >= 0) "+" else "";
            std.debug.print("{s} [0x{x} (base{s}{d})] -> ", .{ label, addr, sign, offset });
        }
    }.run;

    // Level 1: Outer Pointer
    if (outer) |inner_ptr_ref| {
        printAddr("outer ptr", inner_ptr_ref, base_addr);

        // Level 2: Inner Pointer
        if (inner_ptr_ref.*) |int_ref| {
            printAddr("inner ptr", int_ref, base_addr);

            // Level 3: The actual Integer Value
            if (int_ref.*) |val| {
                std.debug.print("int was {}\n", .{val});
            } else {
                std.debug.print("int was null -> STOP\n", .{});
            }
        } else {
            std.debug.print("inner ptr [null] -> STOP\n", .{});
        }
    } else {
        std.debug.print("outer ptr [null] -> STOP\n", .{});
    }
}

pub fn main() void {
    // Capture base address
    var origin: i32 = 0;
    const base_addr = @intFromPtr(&origin);

    std.debug.print("--- Triple-Nullability Cube (Base: 0x{x}) ---\n\n", .{base_addr});

    // Setup variables on the stack
    var middle_null: ?*?i32 = null;

    var val_null: ?i32 = null;
    var middle_to_val_null: ?*?i32 = &val_null;

    var val_one: ?i32 = 1;
    var middle_to_val_one: ?*?i32 = &val_one;

    // V1: Root is null
    std.debug.print("V1: ", .{});
    deepPrint(null, base_addr);

    // V2: Root exists, points to a null pointer
    std.debug.print("V2: ", .{});
    deepPrint(&middle_null, base_addr);

    // V3: Root and Inner exist, but value is null
    std.debug.print("V3: ", .{});
    deepPrint(&middle_to_val_null, base_addr);

    // V4: All layers exist
    std.debug.print("V4: ", .{});
    deepPrint(&middle_to_val_one, base_addr);
}
