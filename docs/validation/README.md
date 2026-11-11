# Validation of the GitHub-ready source tree

The clean repository contains **1,371 mathematical library modules**: 1,132 in
`LocalLaw` and 239 in `SpectralConsequences`. `scripts/KernelReplay.lean` is an
additional verification program, not another mathematical library module.

## Source integrity

All 1,371 comment-free Lean token streams, preserving string literals, were
compared with the previously kernel-checked source bundle. There were **zero
mathematical token changes**. Of these files, 1,359 remain byte-identical;
12 have documentation-comment clarifications naming the later theorems that
discharge intermediate hypotheses. Every one of those 12 files was freshly
compiled in the new root layout, without diagnostics. The original research
outputs were preserved outside the Git source inventory.

See [source-integrity.json](source-integrity.json) for the changed-file list
and aggregate token-inventory digest. Checked artifacts for unchanged sources
were reused only after baseline source/cache validation and artifact SHA-256
verification. The locally migrated cache is ignored by Git; a fresh checkout
compiles its own project artifacts.

## Checked commands

The unified source/placeholder audit passed:

```sh
python3 scripts/check.py --audit-only
```

The portable root configuration loaded successfully with Lake 4.19's bundled
Lake, and `lake env lean --version` selected Lean 4.19.0. The two-library
namespace-glob configuration was additionally tested in a fresh isolated Lake
fixture with sibling and cross-library imports.

The full source-cache validation and explicit kernel replay then passed in
the cleaned repository, through the Lake environment:

```sh
lake --no-cache env python3 scripts/check.py --kernel
```

Result: **1,371 checked cached modules; 13,941 safe mathematical declarations
replayed through Lean's kernel at trust level zero, including every theorem
proof term.** Lean's official replay separately reports 2,495 generated
unsafe/partial implementation auxiliaries. No explicit unsafe/partial source
definition or theorem occurs in either library. No errors, warnings, or
panics occurred. See the complete portable [kernel result](kernel-replay.txt).

The baseline's public axiom audits report only `propext`, `Classical.choice`,
and `Quot.sound`. The checker rejects actual `sorry`, `admit`, `sorryAx`, and
project `axiom` tokens, while ignoring comments and strings. Its source
inventory, scanner, compiler resolution, and atomic temporary-output behavior
also passed targeted checks.

## Dependency and repository checks

Lean is pinned to **4.19.0**. All nine installed dependency Git revisions
matched the committed manifest and had no tracked source modifications.
Mathlib is commit `c44e0c8ee63ca166450922a373c7409c5d26b00b` (`v4.19.0`).
Existing compiled dependencies were used read-only for this local check;
network fetching from a fresh clone was not needed. GitHub Actions execution
will occur after the repository is pushed.

All Markdown relative links resolve. The workflow and citation files parse
as YAML; the Lake manifest/configuration pins agree. The publishable source,
scripts, documentation and configuration contain no user-specific absolute
paths. The updated five-page guide preserves all 31 checked qualified Lean
names and passed visual QA without TeX layout diagnostics.

The necessary explicit modification of printed Definition 2.6, and the weaker
sufficient intermediate Section 7 estimates, remain documented in
[formalization.md](../formalization.md) and [paper-match-audit.txt](../paper-match-audit.txt).
