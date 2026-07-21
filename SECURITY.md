# Security Policy

## Supported versions

Security and correctness fixes target the current `main` branch. Published
snapshots before 1.0 do not receive a guaranteed backport window.

## Reporting a vulnerability

Do not open a public issue for vulnerabilities that could expose secrets,
corrupt proof or certificate verification, violate memory safety, or permit
untrusted input to execute code. Use GitHub private vulnerability reporting for
this repository. If that surface is unavailable, contact the repository owner
through their GitHub profile without including exploit details in a public post.

Include the affected revision, input or proof artifact, expected behavior,
observed behavior, and the smallest reproduction you can safely provide.

## Correctness defects

Unsound theorem, SAT, SMT, model-checking, or certificate results are treated as
security-relevant correctness defects. A result reported as `verified`, `proven`,
`unsat`, or `equivalent` without sufficient evidence should be reported even when
it does not create a conventional confidentiality or code-execution impact.

## Scope limits

The repository is pre-1.0 research software. Passing tests do not establish
adversarial parser hardening, side-channel resistance, formal verification of
the Zig implementation, or suitability for safety-critical deployment.
