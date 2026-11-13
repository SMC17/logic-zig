const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    const mod = b.addModule("logic", .{
        .root_source_file = b.path("src/root.zig"),
        .target = target,
        .optimize = optimize,
    });

    // Main umbrella CLI
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

    // Flagship spin-offs — each pins a profile with unique tradeoffs
    const spinoffs = [_]struct { name: []const u8, path: []const u8 }{
        .{ .name = "logic-agent", .path = "spinoffs/logic-agent/main.zig" },
        .{ .name = "logic-sat", .path = "spinoffs/logic-sat/main.zig" },
        .{ .name = "logic-hwmcc", .path = "spinoffs/logic-hwmcc/main.zig" },
        .{ .name = "logic-cert", .path = "spinoffs/logic-cert/main.zig" },
        .{ .name = "logic-smt", .path = "spinoffs/logic-smt/main.zig" },
        .{ .name = "logic-ctl", .path = "spinoffs/logic-ctl/main.zig" },
    };
    for (spinoffs) |sp| {
        const sp_exe = b.addExecutable(.{
            .name = sp.name,
            .root_module = b.createModule(.{
                .root_source_file = b.path(sp.path),
                .target = target,
                .optimize = optimize,
                .imports = &.{
                    .{ .name = "logic", .module = mod },
                },
            }),
        });
        b.installArtifact(sp_exe);
    }

    // IPASIR shared library
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

    const ipasir_abi = b.addExecutable(.{
        .name = "ipasir-abi-test",
        .root_module = b.createModule(.{ .target = target, .optimize = optimize }),
    });
    ipasir_abi.root_module.link_libc = true;
    ipasir_abi.root_module.addIncludePath(b.path("include"));
    ipasir_abi.root_module.addCSourceFile(.{ .file = b.path("tests/ipasir_abi.c"), .flags = &.{ "-std=c11", "-Wall", "-Wextra", "-Werror" } });
    ipasir_abi.root_module.linkLibrary(ipasir_lib);
    const run_ipasir_abi = b.addRunArtifact(ipasir_abi);
    test_step.dependOn(&run_ipasir_abi.step);

    const lib_step = b.step("lib", "Build IPASIR shared library");
    lib_step.dependOn(&b.addInstallArtifact(ipasir_lib, .{}).step);

    const spin_step = b.step("spinoffs", "Build all flagship spin-off CLIs");
    spin_step.dependOn(b.getInstallStep());

    // External gravity: IPASIR consumer example
    const ipasir_ex = b.addExecutable(.{
        .name = "ipasir-consumer",
        .root_module = b.createModule(.{
            .root_source_file = b.path("examples/ipasir_consumer.zig"),
            .target = target,
            .optimize = optimize,
            .imports = &.{
                .{ .name = "logic", .module = mod },
            },
        }),
    });
    b.installArtifact(ipasir_ex);
}
