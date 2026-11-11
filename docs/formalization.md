# Formalized statements and proof map

This repository formalizes the weak local law and the two conditional spectral conclusions in Huang–Yau, *Spectrum of Random d-regular Graphs Up to the Edge*, [arXiv:2102.00963v3](https://arxiv.org/abs/2102.00963v3) ([bundled PDF](paper/2102.00963v3.pdf)). The final spectral statements use an explicit correction to Definition 2.6, explained below. They do not assume a local law, a fluctuation estimate, a reference-class certificate, or a resampling certificate.

The source is split into two Lean libraries:

| Library | Content | Entry points |
| --- | --- | --- |
| `LocalLaw` | Graph and resolvent models, tree extensions, switching, stability, improvement, and the uniform weak local law | [Main](../LocalLaw/Main.lean), [Audit](../LocalLaw/Audit.lean), [SourceTheorem42](../LocalLaw/SourceTheorem42.lean) |
| `SpectralConsequences` | Eigenvectors, counting and quantiles, Section 7 fluctuation averaging and confinement, arbitrary-core reference classes, and the final paper-form statements | [Main](../SpectralConsequences/Main.lean), [Audit](../SpectralConsequences/Audit.lean), [FullPaperTheorems](../SpectralConsequences/FullPaperTheorems.lean) |

There are 1,371 registered project modules: 1,132 in `LocalLaw` and 239 in `SpectralConsequences`, including each library's `Main` and `Audit`.

## Final probability space

`RegularGraph N d` is the finite type of **simple** graphs on `Fin N` with every degree exactly `d`. Its matrix is

\[
H=\frac{A}{\sqrt{d-1}}.
\]

Fix an integer \(d\ge 3\) and \(0<c<1\). The literal paper structural event has

\[
R=\frac c4\frac{\log N}{\log(d-1)},
\qquad
\operatorname{excess}(B_R(o))\le\omega\quad\text{for every }o,
\]

and at most \(N^c\) centers whose radius-\(R\) ball is not a tree. [PaperEvent](../SpectralConsequences/PaperEvent.lean) defines the real-radius event `PaperStructural` and proves exact equivalence with the integer-floor implementation. The definition includes reachability, so vertices in different components cannot enter a ball through the totalized natural-distance function.

The final theorems use the actual uniform law on

```lean
PaperGraph N d c := {g : RegularGraph N d // PaperStructural c (paperOmega d) g}
```

They prove this subtype is eventually nonempty whenever `RegularGraph N d` is nonempty. This explicit admissibility hypothesis expresses the requirement that the original uniform regular-graph ensemble exists. The subtype law is proved exactly equal to the conditional ratio under the original uniform ensemble; conditioning is not justified by division by zero.

For every real failure exponent \(C\), the failure probability is eventually at most \(N^{-C}\). The threshold in \(N\) may depend on the fixed parameters and \(C\). The results do not assert uniformity for a degree growing with \(N\).

## Theorem 1.2: weak rigidity

[`SpectralConsequences.full_paper_theorem_1_2`](../SpectralConsequences/FullPaperTheorems.lean) proves that there is \(\alpha>0\) such that, with the preceding all-polynomial conditional probability,

\[
\max_{2\le i\le N}|\lambda_i-\gamma_i|\le N^{-\alpha}.
\]

The eigenvalues are the actual descending Hermitian eigenvalues of \(H\), with multiplicities. Only the distinguished first constant-vector mode is excluded. Other eigenvalues coinciding with it are still included; no connectivity or simple-spectrum assumption is imposed. The classical locations satisfy the exact Kesten–McKay equation

\[
\int_{\gamma_i}^{2}\rho_d(x)\,dx=\frac iN,
\qquad
\rho_d(x)=\left(1+\frac1{d-1}-\frac{x^2}{d}\right)^{-1}
\frac{\sqrt{(4-x^2)_+}}{2\pi}.
\]

[PaperTheorem12](../SpectralConsequences/PaperTheorem12.lean) supplies the one-based rank conversion and the exact quantile identity. The construction permits the positive rate

\[
\alpha=\frac{\min(c/2,1/4)}{8192}.
\]

This is a weak positive-power result, as in the numbered theorem. It does not claim an optimal \(N^{-2/3}\) edge scale or the optional numerical exponent discussed in the paper.

## Theorem 1.4: all eigenvectors

[`SpectralConsequences.full_paper_theorem_1_4`](../SpectralConsequences/FullPaperTheorems.lean) proves, with the same type of conditional probability, that every complex eigenpair satisfies

\[
Hv=\lambda v
\quad\Longrightarrow\quad
\|v\|_\infty\le
\frac{(\log N)^{151}}{\sqrt N}
\left(\sum_j|v_j|^2\right)^{1/2}.
\]

`PaperAllEigenvectors` quantifies over every \(\lambda\in\mathbb C\) and every complex vector, including zero. The proof derives eigenvalue reality from Hermitian symmetry for nonzero vectors. It applies to every vector in each eigenspace, with no chosen eigenbasis or normalization premise. Both norms are the actual finite-dimensional norms; the fixed degree-dependent coefficient in the earlier estimate is absorbed into the additional logarithm. See [PaperAllEigenvectors](../SpectralConsequences/PaperAllEigenvectors.lean), [PaperTheorem14](../SpectralConsequences/PaperTheorem14.lean), and the resolvent [EigenvectorWard](../SpectralConsequences/EigenvectorWard.lean) criterion.

Both final theorems also have `_ratio` companions in [FullPaperTheorems](../SpectralConsequences/FullPaperTheorems.lean).

## Necessary correction to Definition 2.6

The printed Definition 2.6 asks for a positive constant diagonal lower bound for **every** \(z\in\mathbb C_+\). That cannot hold for an actual bounded self-adjoint graph resolvent: at \(z=iY\),

\[
|G_{ii}(iY)|\le \frac1Y\longrightarrow0.
\]

[`no_global_positive_diagonal_lower_bound`](../SpectralConsequences/PaperDefinitionSanity.lean) proves this obstruction in Lean. Consequently the project does not claim literal equivalence with that impossible printed condition. It uses the consistent global relative lower bound

\[
\frac{|m_d(z)|}{C}\le |G_{ii}(z)|,
\]

along with the entry-decay and imaginary-part upper estimates. [PaperBoundedReference](../SpectralConsequences/PaperBoundedReference.lean) proves the usual positive constant upper and lower diagonal bounds on every fixed bounded spectral region.

The corrected class still quantifies over **possibly infinite cores** and all upper-half-plane spectral parameters. [AllCorePaperComplexity](../SpectralConsequences/AllCorePaperComplexity.lean) uses finite deficit support and an actual finite feedback-edge set whose deletion leaves a forest, with their total budget at most \(\omega\). [AllCoreReferenceLimit](../SpectralConsequences/AllCoreReferenceLimit.lean) passes the finite-core estimates to actual infinite-core resolvents by finite exhaustion and strong resolvent convergence. [PaperReferenceThreshold](../SpectralConsequences/PaperReferenceThreshold.lean) proves equivalence with the finite reference class.

`paperOmega` is chosen as a genuine maximal positive integer for this corrected all-core class. Its equality with `LocalLaw.finiteOmega` is proved by `paperOmega_eq_finiteOmega`; it is not a definition or an extra hypothesis. This qualification is part of the mathematical statement of the formalization.

## Local law and the route to the spectral conclusions

[`LocalLaw.source_theorem_4_2`](../LocalLaw/SourceTheorem42.lean) proves the actual uniform local law with real parameters

\[
a\ge12,\qquad b\ge25a,\qquad0<\beta\le c/32,
\qquad \eta\ge\frac{(\log N)^b}{N}.
\]

The conclusion is simultaneous in all upper-half-plane spectral parameters above this floor and uses the actual finite-radius extension model. Its error and weak self-consistency control are the defined paper quantities, with a fixed degree-dependent multiplicative constant. The final spectral wrappers choose fixed admissible auxiliary parameters internally.

The main proof components are:

1. **Finite and infinite reference models.** Exact Schur complements identify finite inherited-deficit extension matrices with genuine tree-extension resolvents. The semicircle and Kesten–McKay functions are identified with their density integrals. The arbitrary-core extension is connected to finite restrictions by operator convergence, rather than an assumed model estimate.
2. **Switching stability and improvement.** The actual local switching is implemented on simple regular graphs. Its own finite sampling law, inverse transformation, and reversibility are proved. The formalization does not identify this sampler with an alternative multigraph or configuration-model sampler. Finite-rank inverse identities, partial endpoint models, deficit restoration, leaf completion, and finite-star lifting establish the graph-specific stability statements without assuming that an arbitrary new local model has the required reference class.
3. **The local-law bootstrap.** Exact retained Schur identities, deterministic old-reference weights, conditional concentration, near/far row bounds, cavity residuals, parameter continuity, and reversible probability transfer improve the weak control. A spectral grid and continuity produce the simultaneous local law. See [SourceFirstStageProof](../LocalLaw/SourceFirstStageProof.lean), [SourceStrongDefectReduction](../LocalLaw/SourceStrongDefectReduction.lean), and [SourceTheorem42Reduction](../LocalLaw/SourceTheorem42Reduction.lean).
4. **Delocalization.** A diagonal Green-function cap from the local law, evaluated at the spectral floor, combines with the eigenvector resolvent inequality. No Section 7 high-moment estimate is required for this step.
5. **Section 7 fluctuation averaging and confinement.** Genuine labelled-graph conditional means and reversible integration-by-parts moments control the corrected cavity and trace residuals. Sampling-exit estimates preserve the original work-event thresholds. The trivial constant-vector pole is cancelled explicitly; the corrected trace is a positive sum over all remaining eigenvalues. Scalar stability then excludes nontrivial eigenvalues outside a shrinking edge neighborhood. See [SourceActualHighMoments](../SpectralConsequences/SourceActualHighMoments.lean), [SourceMomentRecurrence](../SpectralConsequences/SourceMomentRecurrence.lean), [SourceGeometricSwitchExit](../SpectralConsequences/SourceGeometricSwitchExit.lean), [TrivialCorrectionSpectral](../SpectralConsequences/TrivialCorrectionSpectral.lean), and [SourceExteriorResidualBound](../SpectralConsequences/SourceExteriorResidualBound.lean).
6. **Counting and quantiles.** The local law gives an empirical CDF bound by Poisson smoothing against the normalized Kesten–McKay density. Confinement controls the edges, and the interval-mass lower bound of order \(t^{3/2}\) converts CDF control into the stated weak rigidity. See [CDFComparison](../SpectralConsequences/CDFComparison.lean), [KestenMcKayQuantiles](../SpectralConsequences/KestenMcKayQuantiles.lean), and [SourceRigidityAssembly](../SpectralConsequences/SourceRigidityAssembly.lean).

Some intermediate estimates are deliberately coarser than the displayed estimates in the paper. In particular, the Section 7 moment/drift implementation retains a fixed logarithmic loss, including terms of the form \((\log N)^{6a+7}\varepsilon^2\). It proves the moment and confinement bounds needed for a positive weak rigidity exponent; it does not claim the paper's sharper log-free intermediate formula verbatim. The local-law improvement likewise permits sufficient fixed constants and logarithmic losses. These are proved estimates, not remaining assumptions in the final theorems.

The sharp full-domain form of Theorem 7.1, the unconditioned structural-complement discussion, Theorem 1.3, optimal rigidity, and eigenvector distribution or universality statements are not claimed by the two final entry points.

## Verification and further reading

[BUILDING.md](BUILDING.md) gives the reproducible build and kernel-replay command. The audit checks all 1,371 registered modules. The completed replay selected 13,941 safe project declarations and rechecked their stored terms through Lean's kernel at trust level zero, starting from the Mathlib and `Lean.Replay` environment. Lean's replay excludes 2,495 unsafe or partial compiler implementation auxiliaries. This distinction is explicit; it is not a claim that importing compiled files alone rechecks every proof.

The public theorem axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`. For exact elaborated statement types and a compact source comparison, see [public-statements.txt](public-statements.txt) and [paper-match-audit.txt](paper-match-audit.txt). The longer [FormalizationGuide.pdf](FormalizationGuide.pdf) and [proof-map.txt](proof-map.txt) give additional mathematical navigation.
