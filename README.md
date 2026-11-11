# Random regular graph local laws in Lean

This repository is a **Lean 4 formalization of main results** of Jiaoyang Huang
and Horng-Tzer Yau,
[Spectrum of Random d-regular Graphs Up to the Edge](docs/paper/2102.00963v3.pdf):
weak polynomial eigenvalue rigidity (Theorem 1.2), delocalization of all
eigenvectors (Theorem 1.4), and the underlying local law (a generalized version
of Theorem 4.2) for fixed-degree random regular graphs. The statements use the
explicit reference-definition correction described below.

The unmodified [arXiv v3 PDF](docs/paper/2102.00963v3.pdf), dated 2 February 2025,
is included for comparison with the Lean statements and proofs. See the
[arXiv record](https://arxiv.org/abs/2102.00963v3) and the
[article attribution and license](docs/paper/README.md).

**Reference-definition modification.** The printed Definition 2.6 asks for a
positive constant diagonal Green-function lower bound on all of the upper
half-plane. The project proves that this is impossible as the imaginary part
tends to infinity and explicitly replaces it by a lower bound relative to
`|m_d(z)|`. The spectral results use the maximal reference threshold for that
corrected definition. Constant diagonal bounds on bounded spectral regions
are proved. See [the mathematical scope](docs/formalization.md) and the
[detailed paper comparison](docs/paper-match-audit.txt).

## Build

The toolchain is **Lean 4.19.0**. Mathlib and its dependencies are pinned in
`lake-manifest.json`; Mathlib is pinned to commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b` (`v4.19.0`).

After installing [elan](https://github.com/leanprover/elan), run:

```sh
lake exe cache get
lake env python3 scripts/check.py --kernel
```

The checker validates the complete module registry, rejects proof placeholders
and project axioms, builds the libraries, and replays every safe mathematical
declaration through Lean's kernel at trust level zero. It reports generated
unsafe/partial implementation auxiliaries separately. `lake build` is also
supported for the normal Lake build and editor workflow.

See [BUILDING](docs/BUILDING.md) for offline installation overrides, cache
behavior, and validation details. Python 3.9 or newer is required by the
standalone checker; it uses only the standard library.
The [validation record](docs/validation/README.md) documents the source-preserving
cleanup and successful full-project kernel replay.

## Public results

All declarations below are in namespace `SpectralConsequences`, except the
local law in namespace `LocalLaw`.

| Result | Entry point |
| --- | --- |
| Generalized Theorem 4.2 local law | [`LocalLaw.source_theorem_4_2`](LocalLaw/SourceTheorem42.lean) |
| Theorem 1.2 weak eigenvalue rigidity | [`full_paper_theorem_1_2`](SpectralConsequences/FullPaperTheorems.lean) |
| Theorem 1.4 all-eigenvector delocalization | [`full_paper_theorem_1_4`](SpectralConsequences/FullPaperTheorems.lean) |
| Genuine Section 7 high moments | [`source_actual_high_moment_bounds`](SpectralConsequences/SourceActualHighMoments.lean) |
| Corrected all-core reference maximum | [`paperOmega`](SpectralConsequences/PaperReferenceThreshold.lean) |

The final spectral statements assume `d ≥ 3`, `0 < c < 1`, and admissibility
of the regular-graph ensemble. They prove eventual nonemptiness of the
structural conditioning event and use its actual uniform law. No local-law,
reference, moment, tail, or probability certificate remains as a final input.

The rigidity rate can be chosen as `min(c/2, 1/4) / 8192`. Delocalization has
the homogeneous bound `(log N)^151 / sqrt N` for every complex eigenpair.
The intermediate Section 7 estimates permit fixed logarithmic losses and
give the exterior confinement needed for weak rigidity; the sharp full-domain
Theorem 7.1 and the separate numerical `0.01` remark are not claimed.

## Repository layout

```text
LocalLaw/                 Local-law foundation; Main and Audit entry points
SpectralConsequences/     Spectral, moment, and corrected all-core proofs
scripts/check.py          Portable checked build and inventory audit
scripts/KernelReplay.lean Explicit kernel replay driver
docs/                     Statements, proof map, comparison, guide, validation
docs/paper/               Unmodified arXiv v3 article and attribution
```

The two `Main.lean` files explicitly register all 1,371 mathematical library
modules. Intermediate interface modules may take estimates as hypotheses;
the final public theorems construct those hypotheses from proved estimates.

For review, start with [the exact public types](docs/public-statements.txt),
the [proof map](docs/proof-map.txt), and the
[formalization guide](docs/FormalizationGuide.pdf).

## Contributing

See [CONTRIBUTING](CONTRIBUTING.md). Preserve the stated mathematical scope,
add new modules to the appropriate registry, and run the kernel check before
submitting proof changes.

## License and citation

This project's source code is released under the [MIT License](LICENSE).
The bundled article is licensed separately under
[CC BY-NC-ND 4.0](https://creativecommons.org/licenses/by-nc-nd/4.0/);
see its [attribution notice](docs/paper/README.md).
Lean, Mathlib, and their dependencies retain their own licenses; their source
and compiled binaries are not vendored here. See [CITATION.cff](CITATION.cff)
for the mathematical reference.
