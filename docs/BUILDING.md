# Building and checking

Run commands from the repository root. The project uses **Lean 4.19.0** and the Mathlib commit

```text
c44e0c8ee63ca166450922a373c7409c5d26b00b
```

[`lean-toolchain`](../lean-toolchain) selects the Lean version. The root Lake configuration and committed `lake-manifest.json` pin Mathlib and its transitive dependencies. Do not run `lake update` for a reproducible check: that command is for intentionally changing dependency pins.

## Recommended check

Install [elan](https://github.com/leanprover/elan) and Python 3.9 or newer. The checker uses the standard-library `fcntl` file lock and runs on Linux, macOS, or WSL. From a fresh checkout with network access, fetch the pinned dependencies and their compiled Mathlib cache:

```sh
lake exe cache get
lake env python3 scripts/check.py --kernel
```

The first command downloads dependencies and compiled dependency artifacts. The second is the primary project check. It validates the source/module inventory, compiles the registered project sources against the pinned dependencies, checks the audit output, and runs the project declaration replay in [`scripts/KernelReplay.lean`](../scripts/KernelReplay.lean). A project build can take substantially longer than a single-file Lean check.

The two library targets are also available through ordinary Lake:

```sh
lake build LocalLaw SpectralConsequences
```

This compiles the library entry points and their imports. It does not replace the additional inventory and declaration-replay checks performed by `scripts/check.py --kernel`.

## Library layout

The source directories at the repository root are the Lean module roots:

```text
LocalLaw/                 # 1,132 registered modules, including Main and Audit
SpectralConsequences/     #   239 registered modules, including Main and Audit
scripts/check.py          # source build and audit driver
scripts/KernelReplay.lean # explicit project declaration replay
docs/                    # statements, proof map, and mathematical guide
```

Each library has its namespace as the Lake `roots` value and a namespace-submodule glob: `LocalLaw.+` or `SpectralConsequences.+`. These globs build every source module, including `Main` and `Audit`, and correctly handle sibling and cross-library imports. No top-level `LocalLaw.lean` or `SpectralConsequences.lean` aggregate file is needed. Globs listing only `Main` and `Audit` do not make the sibling modules buildable in Lake 4.19.

`Main.lean` explicitly registers every project source. `Audit.lean` imports the relevant closure and prints axiom reports for the main results and critical intermediate theorems. Generated `.olean`, `.ilean`, native, trace, and cache files belong under `.lake/`; dependencies and generated artifacts are not vendored into the source repository.

## What the kernel check does

`--kernel` goes beyond importing existing `.olean` files with `--trust=0`. The replay program:

1. Imports both project audits and selects declarations by their originating project module, including private declarations and declarations outside the module's namespace.
2. Starts a fresh environment containing Mathlib and `Lean.Replay`, with trust level zero and no project declarations.
3. Replays the safe declarations through Lean's official `Environment.replay`, in module dependency order. Between modules it resets elaboration bookkeeping while retaining the checked kernel environment.
4. Checks that each selected safe declaration, and each required public theorem, is present in the checked kernel environment and prints an explicit completion marker.

The recorded completed run covered **1,371 project modules and 13,941 safe declarations**. Lean's replay skipped **2,495 unsafe/partial compiler implementation auxiliaries**. These are reported separately; the count is not concealed as a claim that all imported implementation code was replayed. The public theorem axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`. Mathlib and Lean are the pinned dependency baseline, rather than additional project modules replayed by this script.

The driver treats a missing completion marker, a replay error, or a panic as a failed verification, even if a subprocess were to return exit status zero.

## Existing compiled dependencies and offline use

The checker can use an already installed, compiled checkout of the pinned Mathlib revision. It does not need a user-specific filesystem path in the repository:

```sh
MATHLIB_ROOT=/absolute/path/to/mathlib \
LEAN_BIN=/absolute/path/to/lean \
python3 scripts/check.py --kernel
```

`MATHLIB_ROOT` is the **Mathlib checkout directory**, with its compiled `.lake/build/lib/lean` cache. Its dependency packages must also be available, either beside the checkout in a Lake packages directory or in its own `.lake/packages` directory. `LEAN_BIN` is the Lean **executable**, not its containing directory, and must be compatible with Lean 4.19.0. `BUILD_DIR` can select a separate project output directory; the default is `.lake/build/lib/lean`.

For an inventory and placeholder scan without Lean compilation:

```sh
python3 scripts/check.py --audit-only
```

To validate through Lake entirely offline, preload **all** manifest-pinned dependency checkouts and the compatible compiled caches into the local ignored `.lake/packages` directory. Then use:

```sh
lake --no-cache --wfail build LocalLaw SpectralConsequences
lake env python3 scripts/check.py --kernel
```

`--no-cache` disables artifact downloads; it does not supply missing package checkouts. Lake can attempt to obtain a missing dependency, so an offline environment must already contain every package from the committed manifest. Do not symlink a shared dependency tree into a writable Lake build if that shared tree must remain untouched: Lake may write configuration or build artifacts there. Use private copies, filesystem copy-on-write clones where available, or the checker's explicit read-only dependency-path mode.

## Results and scope

Use the process exit status and the final explicit replay success marker to assess a run. A cached source build alone is not the declaration replay. The exact public theorem statements, necessary correction to printed Definition 2.6, and the scope of the fixed logarithmic losses are documented in [formalization.md](formalization.md). See also [paper-match-audit.txt](paper-match-audit.txt) and [public-statements.txt](public-statements.txt).
