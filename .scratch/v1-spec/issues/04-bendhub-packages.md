# How do BendHub packages depend on each other, and what does publishing need?

Type: research
Status: resolved
Blocked by: none
Map: [bend-http v1 spec](../map.md)

## Question

From `bend guide`, `bend --help` and the BendHub terms: can a published package import another hub package by name and version? How are versions and hashes pinned? Can laws and their proofs live in separate files or packages? What does `--verdict` add over a normal check, and how slow is it? Any size limits, licence rules or naming rules? Output: the facts needed to decide the package layout.

## Answer

Full findings: branch `research/bendhub-packages`, file `.scratch/v1-spec/research/04-bendhub-packages.md` (commit a99d2a9; not merged).

- Packages import hub packages by `name@a.b.c.d/x.bend` or `0x<hash>/x.bend`; publishing ships the import line, not the dependency.
- Packages never change: the hash covers every file including `LICENSE`. Versions have four numbers and only go up; `bend link` can't re-point an existing version.
- Laws and proofs can be in separate files, but `--publish` fails on any open law, so both ship in the same package (entry = `PROOF.bend` or a file importing it).
- `--publish` doesn't run `--verdict` or reject unsafe/foreign code: our "all proven + `--verdict`" bar is our own release gate. `--verdict` needs Lean 4.34.0 (not installed); not timed.
- `LICENSE` beside the entry file, starting `SPDX-License-Identifier: MIT`; without one the package is MIT-0. No hard size limit (proof-of-work ≈5 s per 256 KiB).
- Publishing by hash needs no account; by name needs `bend login` (GitHub). Names under 12 characters are auctioned (≥5 USD, 48 h); names of 12+ characters are free. This reopens the naming decision.
