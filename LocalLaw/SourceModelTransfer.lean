import LocalLaw.SourceGreenCaps
import LocalLaw.OffsetStructuralEvent
import LocalLaw.SparseParameterAbsorption
import LocalLaw.EventualGraphMesh
import LocalLaw.ExteriorRate

/-!
# Physical reference replacement and the averaged local-law rate

All reference sensitivity, good diagonal identities and exceptional diagonal
bounds below are proved for the actual pair-neighborhood model. The eventual
wrapper supplies their feedback and sparse-density conditions from the
source parameters and the auxiliary structural event.
-/

open scoped BigOperators
namespace LocalLaw
noncomputable section
local instance sourceTransferDecidable (p : Prop) : Decidable p := Classical.propDecidable p

noncomputable def sourceWidthConstant (B : ℝ) : ℝ := Real.sqrt (2 * B + 3)

theorem sourceWidthConstant_pos (B : ℝ) (hB : 0 ≤ B) : 0 < sourceWidthConstant B := by
  exact Real.sqrt_pos.mpr (by linarith)

theorem source_bounded_width (B : ℝ) (z : ℂ) (ε : ℝ) (hB : ‖z‖ ≤ B) (hε : ε ≤ 1) :
    Real.sqrt (spectralScale z + ε) ≤ sourceWidthConstant B := by
  apply Real.sqrt_le_sqrt
  linarith [spectralScale_le_twice_norm_add_two z]

namespace RegularGraph
variable {N d : ℕ}

theorem pairP_diagonal_eq_reference_of_good (g : RegularGraph N d) (hd : 3 ≤ d)
    (r : ℕ) (z : ℂ) (hz : 0 < z.im) (i : Fin N)
    (hi : i ∉ nonTreeCenters g.graph r) :
    g.P r z (semicircleRoot z) i i = graphKestenMcKayReference d z := by
  have htree : (graphBall g.graph i r).IsTree :=
    not_not.mp (fun hn => hi ((nonTreeCenters_membership g.graph r i).mpr hn))
  apply g.P_reference_diagonal_of_acyclic hd r z hz i
  apply induced_acyclic_mono g.graph _ htree.2
  intro v hv
  exact hv.elim id id

theorem pairP_diagonal_reference_error (g : RegularGraph N d) (hd : 3 ≤ d)
    (r R : ℕ) (hmargin : 4 * r + 1 ≤ R)
    (hballs : ∀ a, graphBallExcess g.graph a R ≤ finiteOmega d)
    (z : ℂ) (hz : 0 < z.im) (i : Fin N) :
    ‖g.P r z (semicircleRoot z) i i - graphKestenMcKayReference d z‖ ≤
      finiteReferenceConstant d + 2 := by
  apply (norm_sub_le _ _).trans
  exact add_le_add (g.pairP_reference_entry_bound hd r R hmargin hballs z hz i i)
    (kestenMcKayTransform_norm_le_two d hd z hz)

/-- Finite deterministic reference replacement, with only numerical feedback
and the explicit exceptional density still displayed. -/
theorem actual_local_law_of_weak_and_sparse (g : RegularGraph N d) (hd : 3 ≤ d)
    (a r R : ℕ) (hN : 0 < N) (hmargin : 4 * r + 1 ≤ R)
    (hballs : ∀ v, graphBallExcess g.graph v R ≤ finiteOmega d)
    (z : ℂ) (hz : 0 < z.im) (B : ℝ) (hzB : ‖z‖ ≤ B)
    (hweak : (graphLocalLawFamily N d a r).weak z g)
    (hε : graphPaperError a d N r z ≤ 1)
    (small : ‖g.Q z - semicircleRoot z‖ * finiteReferenceConstant d *
      coreConvolutionConstant (finiteOmega d) * (4 * (r : ℝ) + 2) ≤ 1 / 2)
    (sparse : (((nonTreeCenters g.graph r).card : ℝ) / (N : ℝ)) *
      (finiteReferenceConstant d + 2) ≤
        scalarScale (spectralScale z) (graphPaperError a d N r z)) :
    ActualGraphLocalLawAt a r (sourceWidthConstant B + pairSensitivityConstant d)
      (sourceWidthConstant B + pairSensitivityConstant d + 1) z g := by
  let ε := graphPaperError a d N r z
  let Ψ := scalarScale (spectralScale z) ε
  have hεnonneg : 0 ≤ ε := graphPaperError_nonnegative a d N r z (by omega) hz.le
  have hΨ : 0 ≤ Ψ := scalarScale_nonneg hεnonneg
  have hroot : 0 < Real.sqrt (spectralScale z + ε) :=
    Real.sqrt_pos.mpr (by linarith [spectralScale_pos hz])
  have hidentity : ε = Ψ * Real.sqrt (spectralScale z + ε) := by
    dsimp only [Ψ, scalarScale]
    field_simp
  have hwidth := source_bounded_width B z ε hzB hε
  have heps : ε ≤ sourceWidthConstant B * Ψ := by
    rw [hidentity]
    exact (mul_le_mul_of_nonneg_left hwidth hΨ).trans_eq (mul_comm _ _)
  have hsensitivity : ∀ i j, ‖g.P r z (g.Q z) i j - g.P r z (semicircleRoot z) i j‖ ≤
      pairSensitivityConstant d * dist (g.Q z) (semicircleRoot z) := by
    intro i j
    simpa only [Complex.dist_eq, pairSensitivityConstant] using
      g.pairP_boundary_uniform_stability hd r R hmargin hballs z (g.Q z) hz
        (g.Q_im_nonnegative z hz) small i j
  have hlocal := boundary_entry_trace (g.G z) (g.P r z) (g.Q z) (semicircleRoot z)
    (graphKestenMcKayReference d z) (nonTreeCenters g.graph r) ε Ψ
    (pairSensitivityConstant d) (finiteReferenceConstant d + 2)
    (pairSensitivityConstant_nonnegative d) (by simpa only [Fintype.card_fin] using hN)
    hweak.2 (by simpa only [Complex.dist_eq] using hweak.1)
    hsensitivity
    (fun i hi => g.pairP_diagonal_eq_reference_of_good hd r z hz i hi)
    (fun i _ => g.pairP_diagonal_reference_error hd r R hmargin hballs z hz i)
  constructor
  · intro i j
    exact (hlocal.1 i j).trans (by nlinarith)
  · rw [regularGraph_transform_sub_eq_average g z (graphKestenMcKayReference d z) hN]
    have hh := hlocal.2
    simp only [Fintype.card_fin] at hh
    exact hh.trans (by nlinarith)

/-- The actual source radii and offset auxiliary count discharge every
deterministic model-transfer condition, uniformly on a bounded spectral disk.
Only the weak local-law event remains as a premise. -/
theorem eventually_actual_local_law_of_source_weak (a b d : ℕ) (c β γ B : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hc : 0 < c)
    (hβ : 0 < β) (hβc : β ≤ c / 32) (hγβ : γ + β ≤ 1) (hB : 0 ≤ B) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (z : ℂ),
      0 < z.im → ‖z‖ ≤ B → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
      offsetStructural (logarithmicRadius (c / 4) d N) (finiteOmega d) 1 ⌊(N : ℝ) ^ γ⌋₊ g →
      (graphLocalLawFamily N d a (logarithmicRadius β d N)).weak z g →
      ActualGraphLocalLawAt a (logarithmicRadius β d N)
        (sourceWidthConstant B + pairSensitivityConstant d)
        (sourceWidthConstant B + pairSensitivityConstant d + 1) z g := by
  let A := sourceWidthConstant B
  let M := finiteReferenceConstant d + 2
  have hA : 0 < A := sourceWidthConstant_pos B hB
  have hM : 0 ≤ M := by dsimp only [M]; linarith [finiteReferenceConstant_ge_one d hd]
  filter_upwards [eventually_source_kernel_feedback a b d β 1
      (2 * finiteReferenceConstant d) (coreConvolutionConstant (finiteOmega d)) ha hb hd hβ
      (by norm_num) (by linarith [finiteReferenceConstant_ge_one d hd])
      (by unfold coreConvolutionConstant; positivity),
    eventually_source_radius_hierarchy a d c β hd hc hβ hβc,
    eventually_paperError_small a b d β ha hb hd hβ,
    eventually_log_ge_nat 1, eventually_log_ge_nat (A * M),
    Filter.eventually_ge_atTop 1] with N hfeedback hradii herror hlog hconstant hN
  intro g z hz hzB hscale haux hweak
  let r := logarithmicRadius β d N
  let R := logarithmicRadius (c / 4) d N
  let ε := graphPaperError a d N r z
  let Ψ := scalarScale (spectralScale z) ε
  have hstruct := offsetStructural_implies_structural haux
  have hmargin : 4 * r + 1 ≤ R := by
    have hlarge := hradii.2.1
    have he := hradii.1
    dsimp only [r, R]
    omega
  have hrR : r ≤ R := by omega
  have hεnonneg : 0 ≤ ε := graphPaperError_nonnegative a d N r z hN hz.le
  have hsmall : ‖g.Q z - semicircleRoot z‖ * finiteReferenceConstant d *
      coreConvolutionConstant (finiteOmega d) * (4 * (r : ℝ) + 2) ≤ 1 / 2 := by
    have hh := hfeedback z (g.Q z) hz hscale (by simpa only [one_mul] using hweak.1)
    convert hh using 1
    dsimp only [r]
    ring
  have hεone : ε ≤ 1 := by
    apply (herror z hz hscale).trans
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hlog)
  have hbad : ((nonTreeCenters g.graph r).card : ℝ) ≤ (N : ℝ) ^ γ := by
    apply (Nat.cast_le.mpr (Finset.card_le_card (nonTreeCenters_mono g.graph hrR))).trans
    exact (Nat.cast_le.mpr hstruct.2).trans (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) γ))
  have hwidth : Real.sqrt (spectralScale z + ε) ≤ A := source_bounded_width B z ε hzB hεone
  have hidentity : ε = Ψ * Real.sqrt (spectralScale z + ε) := by
    have hroot : 0 < Real.sqrt (spectralScale z + ε) :=
      Real.sqrt_pos.mpr (by linarith [spectralScale_pos hz])
    dsimp only [Ψ, scalarScale]
    field_simp
  have hsparse : (((nonTreeCenters g.graph r).card : ℝ) / (N : ℝ)) * M ≤ Ψ := by
    have hh := sparse_error_log_absorption N d a 0 β γ A M
      (nonTreeCenters g.graph r).card hN hd hβ.le hγβ hbad hA hM hlog (by omega) hconstant z hz.le
    simp only [pow_zero, mul_one] at hh
    apply hh.trans
    apply (div_le_iff₀ hA).mpr
    change ε ≤ Ψ * A
    rw [hidentity]
    exact mul_le_mul_of_nonneg_left hwidth (scalarScale_nonneg hεnonneg)
  exact g.actual_local_law_of_weak_and_sparse hd a r R (by omega) hmargin hstruct.1 z hz B hzB
    hweak hεone hsmall hsparse

end RegularGraph
end
end LocalLaw
