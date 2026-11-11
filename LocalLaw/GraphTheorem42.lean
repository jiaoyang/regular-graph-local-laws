import LocalLaw.GraphModel
import LocalLaw.CavityAverage
import LocalLaw.ErrorParameters
import LocalLaw.Theorem42

/-!
# A source-specific conditional Theorem 4.2

The generic theorem is specialized here to actual uniform finite regular
graphs, their physical resolvents and deleted minors, induced pair-ball
boundary models, the physical semicircle branch, regular-tree reference,
and the paper's explicit error definition.

The certificate structure below fixes every one of these identifiers.
This module provides an intermediate interface: its local resampling and
spectral-net fields are hypotheses of the results here. The completed source
theorem, with the resampling and net estimates proved, is in `SourceTheorem42`.
-/

open scoped BigOperators

namespace LocalLaw

/-- The actual paper error with the regular-tree reference inserted. -/
noncomputable def graphPaperError (a d N r : ℕ) (z : ℂ) : ℝ :=
  paperError a d N r z (graphKestenMcKayReference d z).im

theorem graphPaperError_nonnegative (a d N r : ℕ) (z : ℂ)
    (hN : 1 ≤ N) (hz : 0 ≤ z.im) : 0 ≤ graphPaperError a d N r z := by
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  unfold graphPaperError paperError paperBaseError
  exact inflateError_nonnegative
    (baseError_nonnegative (Real.log (N : ℝ)) a d N r z.im _ hlog hz)

/-- All physical identifiers are fixed to the original graph model. The
fields of `data` specify local analytic and resampling hypotheses for this
intermediate interface, rather than a final probability bound. -/
structure GraphLocalLawInputs (N d a r R ω badCount T : ℕ) where
  degreeAtLeastThree : 3 ≤ d
  data : Theorem42Inputs (RegularGraph N d) (Fin N) T
  weight_eq : data.weight = RegularGraph.weight
  structural_eq : data.structural = RegularGraph.structural R ω badCount
  Q_eq : data.Q = fun g z => g.Q z
  G_eq : data.G = fun g z => g.G z
  P_eq : data.P = fun g z w i j => g.P r z w i j
  m_eq : data.m = semicircleRoot
  md_eq : data.md = graphKestenMcKayReference d
  scale_eq : data.s = spectralScale
  error_eq : data.ε = graphPaperError a d N r
  cavity_eq : data.cavity = fun g t i => cavityAtVertex g.graph d (data.net t) i
  badCavity_eq : data.badCavity = fun g _t => nonTreeCenters g.graph R
  badDiagonal_eq : data.badDiagonal = fun g _z => nonTreeCenters g.graph r

/-- The empirical transform minus a reference is the actual mean diagonal
error, with the positive vertex-cardinality condition explicit. -/
theorem regularGraph_transform_sub_eq_average {N d : ℕ} (g : RegularGraph N d)
    (z reference : ℂ) (hN : 0 < N) :
    empiricalTransform g.H z - reference =
      (N : ℝ)⁻¹ • ∑ i : Fin N, (g.G z i i - reference) := by
  have hNzero : (N : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hN)
  have hconstant : (N : ℝ)⁻¹ • (∑ _i : Fin N, reference) = reference := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hNzero, one_smul]
  calc
    empiricalTransform g.H z - reference =
        ((N : ℝ)⁻¹ • ∑ i : Fin N, g.G z i i) - reference := by
      simp only [empiricalTransform, Matrix.trace, Fintype.card_fin,
        Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast, RegularGraph.G,
        Matrix.diag_apply]
    _ = (N : ℝ)⁻¹ • ∑ i : Fin N, (g.G z i i - reference) := by
      rw [Finset.sum_sub_distrib, smul_sub, hconstant]

/-- The actual entrywise and empirical-transform conclusion, with one common
error scale and separate explicit entry/trace constants. -/
def ActualGraphLocalLawAt {N d : ℕ} (a r : ℕ) (Centry Ctrace : ℝ)
    (z : ℂ) (g : RegularGraph N d) : Prop :=
  (∀ i j, ‖g.G z i j - g.P r z (semicircleRoot z) i j‖ ≤
    Centry * scalarScale (spectralScale z) (graphPaperError a d N r z)) ∧
  ‖empiricalTransform g.H z - graphKestenMcKayReference d z‖ ≤
    Ctrace * scalarScale (spectralScale z) (graphPaperError a d N r z)

namespace GraphLocalLawInputs

variable {N d a r R ω badCount T : ℕ}

theorem vertex_positive (D : GraphLocalLawInputs N d a r R ω badCount T) : 0 < N := by
  simpa only [Fintype.card_fin] using D.data.vertexPositive

/-- The abstract rate event is exactly the physical graph rate event under
the source-specific consistency fields. -/
theorem rate_event_iff (D : GraphLocalLawInputs N d a r R ω badCount T)
    (Centry Ctrace : ℝ) (z : ℂ) (g : RegularGraph N d) :
    D.data.RateLocalLawAt Centry Ctrace z g ↔ ActualGraphLocalLawAt a r Centry Ctrace z g := by
  unfold Theorem42Inputs.RateLocalLawAt ActualGraphLocalLawAt
  rw [D.G_eq, D.P_eq, D.m_eq, D.md_eq, D.scale_eq, D.error_eq]
  simp only [Fintype.card_fin]
  rw [regularGraph_transform_sub_eq_average g z (graphKestenMcKayReference d z) D.vertex_positive]

/-- Source-specific local-law implication under the explicit hypotheses
of `D.data`. The completed source probability theorem is assembled separately
in `SourceTheorem42`. -/
theorem graph_theorem_4_2_rate (D : GraphLocalLawInputs N d a r R ω badCount T)
    (A₀ K₀ D₀ : ℝ)
    (upperHalfPlane : ∀ z ∈ D.data.domain, 0 < z.im)
    (width : ∀ z ∈ D.data.domain,
      Real.sqrt (spectralScale z + graphPaperError a d N r z) ≤ A₀)
    (model : ∀ z ∈ D.data.domain, D.data.modelLipschitz z ≤ K₀)
    (sparse : ∀ z ∈ D.data.domain, ∀ g : RegularGraph N d, RegularGraph.structural R ω badCount g →
      (((nonTreeCenters g.graph r).card : ℝ) / (N : ℝ)) * D.data.diagonalBound z ≤
        D₀ * scalarScale (spectralScale z) (graphPaperError a d N r z)) :
    eventMass (RegularGraph.weight (N := N) (d := d)) (fun g => RegularGraph.structural R ω badCount g ∧
      ¬ ∀ z ∈ D.data.domain, ActualGraphLocalLawAt a r (A₀ + K₀) (A₀ + K₀ + D₀) z g) /
      eventMass (RegularGraph.weight (N := N) (d := d)) (RegularGraph.structural R ω badCount) ≤
      (∑ t, ∑ o, (D.data.firstBudget t o + D.data.secondBudget t o)) /
        eventMass (RegularGraph.weight (N := N) (d := d)) (RegularGraph.structural R ω badCount) := by
  have hs : ∀ z ∈ D.data.domain, 0 < D.data.s z := by
    intro z hz
    rw [D.scale_eq]
    exact spectralScale_pos (upperHalfPlane z hz)
  have hε : ∀ z ∈ D.data.domain, 0 ≤ D.data.ε z := by
    intro z hz
    rw [D.error_eq]
    exact graphPaperError_nonnegative a d N r z (Nat.succ_le_of_lt D.vertex_positive)
      (upperHalfPlane z hz).le
  have hwidth : ∀ z ∈ D.data.domain, Real.sqrt (D.data.s z + D.data.ε z) ≤ A₀ := by
    simpa only [D.scale_eq, D.error_eq] using width
  have hsparse : ∀ z ∈ D.data.domain, ∀ g, D.data.structural g →
      (((D.data.badDiagonal g z).card : ℝ) / (Fintype.card (Fin N) : ℝ)) *
        D.data.diagonalBound z ≤ D₀ * scalarScale (D.data.s z) (D.data.ε z) := by
    simpa only [D.structural_eq, D.badDiagonal_eq, D.scale_eq, D.error_eq,
      Fintype.card_fin] using sparse
  have h := D.data.generalized_theorem_4_2_rate A₀ K₀ D₀ hs hε hwidth model hsparse
  simpa only [D.weight_eq, D.structural_eq, D.rate_event_iff] using h

/-- Explicit polynomial high probability for the actual graph objects. The
center count is exactly N; only the O(N²) net-node count needs a grid constant.
The two per-site errors and the structural mass lower bound remain visible. -/
theorem graph_theorem_4_2_polynomial_rate
    (D : GraphLocalLawInputs N d a r R ω badCount T) (A₀ K₀ D₀ : ℝ)
    (upperHalfPlane : ∀ z ∈ D.data.domain, 0 < z.im)
    (width : ∀ z ∈ D.data.domain,
      Real.sqrt (spectralScale z + graphPaperError a d N r z) ≤ A₀)
    (model : ∀ z ∈ D.data.domain, D.data.modelLipschitz z ≤ K₀)
    (sparse : ∀ z ∈ D.data.domain, ∀ g : RegularGraph N d, RegularGraph.structural R ω badCount g →
      (((nonTreeCenters g.graph r).card : ℝ) / (N : ℝ)) * D.data.diagonalBound z ≤
        D₀ * scalarScale (spectralScale z) (graphPaperError a d N r z))
    (q : ℕ) (hq : 3 ≤ q) (Cgrid Dlocal : ℝ) (hCgrid : 0 ≤ Cgrid)
    (hDlocal : 0 ≤ Dlocal)
    (hmass : 1 / 2 ≤ eventMass (RegularGraph.weight (N := N) (d := d)) (RegularGraph.structural R ω badCount))
    (hnode : (T : ℝ) ≤ Cgrid * (N : ℝ) ^ 2)
    (hα : ∀ t o, D.data.firstBudget t o ≤ Dlocal / (N : ℝ) ^ q)
    (hγ : ∀ t o, D.data.secondBudget t o ≤ Dlocal / (N : ℝ) ^ q) :
    eventMass (RegularGraph.weight (N := N) (d := d)) (fun g => RegularGraph.structural R ω badCount g ∧
      ¬ ∀ z ∈ D.data.domain, ActualGraphLocalLawAt a r (A₀ + K₀) (A₀ + K₀ + D₀) z g) /
      eventMass (RegularGraph.weight (N := N) (d := d)) (RegularGraph.structural R ω badCount) ≤
      4 * Cgrid * Dlocal / (N : ℝ) ^ (q - 3) := by
  have hs : ∀ z ∈ D.data.domain, 0 < D.data.s z := by
    intro z hz
    rw [D.scale_eq]
    exact spectralScale_pos (upperHalfPlane z hz)
  have hε : ∀ z ∈ D.data.domain, 0 ≤ D.data.ε z := by
    intro z hz
    rw [D.error_eq]
    exact graphPaperError_nonnegative a d N r z (Nat.succ_le_of_lt D.vertex_positive)
      (upperHalfPlane z hz).le
  have hwidth : ∀ z ∈ D.data.domain, Real.sqrt (D.data.s z + D.data.ε z) ≤ A₀ := by
    simpa only [D.scale_eq, D.error_eq] using width
  have hsparse : ∀ z ∈ D.data.domain, ∀ g, D.data.structural g →
      (((D.data.badDiagonal g z).card : ℝ) / (Fintype.card (Fin N) : ℝ)) *
        D.data.diagonalBound z ≤ D₀ * scalarScale (D.data.s z) (D.data.ε z) := by
    simpa only [D.structural_eq, D.badDiagonal_eq, D.scale_eq, D.error_eq,
      Fintype.card_fin] using sparse
  have hmass' : 1 / 2 ≤ eventMass D.data.weight D.data.structural := by
    simpa only [D.weight_eq, D.structural_eq] using hmass
  have h := D.data.generalized_theorem_4_2_polynomial_rate A₀ K₀ D₀ hs hε hwidth
    model hsparse N q D.vertex_positive hq Cgrid 1 Dlocal hCgrid (by norm_num)
    hDlocal hmass' hnode (by simp) hα hγ
  simpa only [D.weight_eq, D.structural_eq, D.rate_event_iff, mul_one] using h

end GraphLocalLawInputs

end LocalLaw
