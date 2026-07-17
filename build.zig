const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    const mod = b.addModule("logic", .{
        .root_source_file = b.path("src/root.zig"),
        .target = target,
        .optimize = optimize,
    });

    const exe = b.addExecutable(.{
        .name = "logic-zig",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/main.zig"),
            .target = target,
            .optimize = optimize,
            .imports = &.{
                .{ .name = "logic", .module = mod },
            },
        }),
    });
    b.installArtifact(exe);

    // IPASIR shared library (C ABI) — root at src/ so relative imports resolve
    const ipasir_lib = b.addLibrary(.{
        .name = "ipasirlogic",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/ipasir_lib_root.zig"),
            .target = target,
            .optimize = optimize,
        }),
        .linkage = .dynamic,
    });
    ipasir_lib.root_module.link_libc = true;
    b.installArtifact(ipasir_lib);

    const run_cmd = b.addRunArtifact(exe);
    run_cmd.step.dependOn(b.getInstallStep());
    if (b.args) |args| run_cmd.addArgs(args);
    const run_step = b.step("run", "Run logic-zig CLI");
    run_step.dependOn(&run_cmd.step);

    const unit_tests = b.addTest(.{
        .root_module = mod,
    });
    const run_unit = b.addRunArtifact(unit_tests);
    const test_step = b.step("test", "Run unit tests");
    test_step.dependOn(&run_unit.step);

    const integration = b.createModule(.{
        .root_source_file = b.path("tests/integration_test.zig"),
        .target = target,
        .optimize = optimize,
        .imports = &.{
            .{ .name = "logic", .module = mod },
        },
    });
    const integration_tests = b.addTest(.{
        .root_module = integration,
    });
    const run_integration = b.addRunArtifact(integration_tests);
    test_step.dependOn(&run_integration.step);
    const integration_step = b.step("integration", "Run integration tests");
    integration_step.dependOn(&run_integration.step);

    const lib_step = b.step("lib", "Build IPASIR shared library");
    lib_step.dependOn(&b.addInstallArtifact(ipasir_lib, .{}).step);
}
