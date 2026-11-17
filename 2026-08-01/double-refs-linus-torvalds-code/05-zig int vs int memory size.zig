const std = @import("std");

pub fn main() void {
    std.debug.print("--- Value Optionality (Uses a Tag) ---\n", .{});
    std.debug.print("size of i32:     {} bytes\n", .{@sizeOf(i32)});
    std.debug.print("size of ?i32:    {} bytes (Larger!)\n", .{@sizeOf(?i32)});

    std.debug.print("\n--- Pointer Optionality (Optimized) ---\n", .{});
    std.debug.print("size of *i32:    {} bytes\n", .{@sizeOf(*i32)});
    std.debug.print("size of ?*i32:   {} bytes (Same size!)\n", .{@sizeOf(?*i32)});

    // Demonstrate distinguishing 0 from null
    var maybe_int: ?i32 = 0;
    if (maybe_int) |val| {
        std.debug.print("\nmaybe_int is present and its value is: {}\n", .{val});
    }

    maybe_int = null;
    if (maybe_int == null) {
        std.debug.print("maybe_int is now null, which is different from 0.\n", .{});
    }
}
