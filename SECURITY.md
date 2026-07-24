# Security Policy

## Reporting a Vulnerability

Do not open a public issue with exploit details. Use GitHub Security Advisories
or private vulnerability reporting for the canonical repository:

[https://github.com/alabsystems/Clean/security/advisories/new](https://github.com/alabsystems/Clean/security/advisories/new)

If that form is unavailable to you, open a minimal public issue that requests a
private security contact without including exploit details.

## Supported Versions

Security support is best-effort for `main` and the latest tagged core Clean
release. There is no response-time SLA.

Core Clean releases use `vX.Y.Z` tags. Mathverse Library releases use
`mathverse-vX.Y.Z` tags and may publish shard archives. These are separate release
streams: a newer Mathverse Library tag does not imply a newer supported core Clean
tag, and a newer core Clean tag does not imply fresh Mathverse shard artifacts.

## Scope

Security reports should include the affected command, crate, input file, and
the smallest reproduction that demonstrates the issue.

In scope:

- kernel/type-checker soundness vulnerabilities
- CLI, server, and release artifact handling
- Mathverse download and verification tooling
- credential leaks or unsafe handling of local secrets

Proof-trust or soundness concerns that are not exploitable security
vulnerabilities should use normal GitHub Issues and reference the exact
theorem, checker, or CLI path involved. Report them privately first when public
users could be misled by current documentation or release artifacts.
