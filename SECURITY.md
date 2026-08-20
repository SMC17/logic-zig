# Security Policy

## Supported versions

| Version | Supported |
|---------|-----------|
| 0.21.x (main) | Yes |
| < 0.21 | Best-effort |

## Reporting a vulnerability

Please **do not** open a public GitHub issue for security-sensitive reports.

Email the maintainer listed on the GitHub profile for `SMC17`, or open a
[private security advisory](https://github.com/SMC17/logic-zig/security/advisories/new)
on this repository.

Include:

1. Affected version / commit SHA
2. Reproduction steps (minimal CNF, AIGER, or API snippet)
3. Impact assessment (soundness bug vs. crash vs. resource exhaustion)

## Scope

logic-zig is a **logic kernel and research library**, not a networked service.
Relevant classes of issues include:

- Soundness bugs (solver claims UNSAT/SAT incorrectly on a validated instance)
- Memory unsafety in Zig code paths (should be impossible in safe Zig; report if found)
- Path traversal or command injection in CLI file handling
- Proof checker accepting invalid RUP/DRAT traces

Out of scope: theoretical incompleteness of fragments marked `fragment` in the
registry, and performance complaints without a correctness angle.

## Response target

We aim to acknowledge reports within 7 days and ship fixes on `main` for
confirmed soundness issues as soon as a minimal regression test exists.
