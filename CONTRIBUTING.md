# Contributing

Use the pinned Lean toolchain and dependency manifest. Obtain the Mathlib
cache, then run:

```sh
lake env python3 scripts/check.py --kernel
```

The source libraries are `LocalLaw/` and `SpectralConsequences/`. Register new
modules in the corresponding `Main.lean`, and add principal public results
to `Audit.lean`. The build checker rejects missing or unregistered library
modules, import cycles, proof placeholders, and project axioms.

Keep public theorem hypotheses and definitions mathematically explicit.
Preserve the original structural conditioning event, eigenvalue ranks and
multiplicities, and the distinction between the printed and corrected
reference definitions. Document changes in the paper comparison when scope
or intermediate estimates change.

The kernel replay driver checks the complete fixed library inventory and
required principal proofs. Update its inventory count deliberately when
adding or removing modules; do not weaken its panic/error/completion checks.

Generated files, build caches, raw logs, and local research directories are
ignored by Git. Keep portable validation summaries in `docs/validation/`.
Do not commit machine-specific dependency paths or changes to the pinned
manifest unless the dependency update is intentional.
