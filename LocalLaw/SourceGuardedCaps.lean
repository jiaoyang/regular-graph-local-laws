import LocalLaw.LocalReferenceCaps
import LocalLaw.LocalBaseModelBudget
import LocalLaw.IndependentRadiusEvents

/-! # Safe local physical Green caps under the actual source plus event

Full diagonal/edge models and far-boundary deleted diagonal/edge models
belong to the base reference class. Their actual approximation errors and
finite perturbation budgets give entry and inverse-diagonal bounds. Deleted
inverse diagonals near the removed boundary are deliberately not asserted.
-/

noncomputable section
set_option maxHeartbeats 2200000
namespace LocalLaw

local instance sourceGuardedCapsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Only scalar approximation/feedback inequalities; no physical Green cap
is included as a field. -/
structure SourceLocalCapBounds (d r : ℕ) (z q : ℂ) (B Efull Edeleted : ℝ) : Prop where
  feedback : ‖q - semicircleRoot z‖ * finiteReferenceConstant d *
    coreConvolutionConstant (finiteOmega d) * (4 * (r : ℝ) + 2) ≤ 1 / 2
  change : pairSensitivityConstant d * ‖q - semicircleRoot z‖ ≤ 1
  full_error : Efull ≤ 1
  deleted_error : Edeleted ≤ 1
  full_pivot : Efull + pairSensitivityConstant d * ‖q - semicircleRoot z‖ ≤
    1 / (2 * finiteReferenceConstant d * (B + 2))
  deleted_pivot : Edeleted + pairSensitivityConstant d * ‖q - semicircleRoot z‖ ≤
    1 / (2 * finiteReferenceConstant d * (B + 2))

namespace SourceLocalCapBounds
variable {d r : ℕ} {z q : ℂ} {B Efull Edeleted : ℝ}
theorem diameter_feedback (S : SourceLocalCapBounds d r z q B Efull Edeleted) :
    ‖q - semicircleRoot z‖ * finiteReferenceConstant d * coreConvolutionConstant (finiteOmega d) *
      (((4 * r + 1 : ℕ) : ℝ) + 1) ≤ 1 / 2 := by
  convert S.feedback using 1
  push_cast
  ring
end SourceLocalCapBounds

namespace RegularGraph.SourceOmegaPlusWithRadii
variable {N d a rModel rError R ell Cq badCount : ℕ} {C1 B : ℝ} {o : Fin N} {z : ℂ}
variable {g : RegularGraph N d}

theorem local_full_entry_cap
    (h : g.SourceOmegaPlusWithRadii a rModel rError R ell (finiteOmega d) Cq badCount C1 o z)
    (hd : 3 ≤ d) (hz : 0 < z.im) (hmargin : rModel + 1 ≤ R / 8)
    (S : SourceLocalCapBounds d rModel z (g.Q z) B (C1 / Real.log (N : ℝ))
      (C1 * g.sourcePrime a rError z))
    (i j : Fin N) (hij : i = j ∨ g.graph.Adj i j) : ‖g.G z i j‖ ≤ commonGreenEntryCap d := by
  let M := g.pairModel i j rModel
  have hM : M.graph.Connected := pairBall_connected_of_eq_or_adjacent g.graph i j rModel hij
  have hbudget := g.local_pairModel_base_budget rModel (R / 8) hmargin h.structural.1 i j hij
  have happ : ‖g.G z i j - M.extensionGreen (g.Q z) z
      (pairBallLeft g.graph i j rModel) (pairBallRight g.graph i j rModel)‖ ≤ C1 / Real.log (N : ℝ) := by
    rw [g.pairModel_P]
    exact h.full i j
  exact (M.base_reference_approximation_entry_cap hd hM hbudget z (g.Q z) hz
    (g.Q_im_nonnegative z hz) (4 * rModel + 1) (pairBall_distance_bound g.graph i j rModel)
    S.diameter_feedback _ _ _ _ happ S.full_error S.change).trans (sourceGreenEntryCap_le_common d hd)

theorem local_full_pivot_cap
    (h : g.SourceOmegaPlusWithRadii a rModel rError R ell (finiteOmega d) Cq badCount C1 o z)
    (hd : 3 ≤ d) (hz : 0 < z.im) (hB : ‖z‖ ≤ B) (hmargin : rModel + 1 ≤ R / 8)
    (S : SourceLocalCapBounds d rModel z (g.Q z) B (C1 / Real.log (N : ℝ))
      (C1 * g.sourcePrime a rError z)) (i : Fin N) :
    ‖(g.G z i i)⁻¹‖ ≤ sourceGreenPivotCap d B := by
  let M := g.pairModel i i rModel
  have hM : M.graph.Connected := pairBall_connected_of_eq_or_adjacent g.graph i i rModel (Or.inl rfl)
  have hbudget := g.local_pairModel_base_budget rModel (R / 8) hmargin h.structural.1 i i (Or.inl rfl)
  have happ : ‖g.G z i i - M.extensionGreen (g.Q z) z
      (pairBallLeft g.graph i i rModel) (pairBallLeft g.graph i i rModel)‖ ≤ C1 / Real.log (N : ℝ) := by
    change ‖g.G z i i - M.extensionGreen (g.Q z) z
      (pairBallLeft g.graph i i rModel) (pairBallRight g.graph i i rModel)‖ ≤ _
    rw [g.pairModel_P]
    exact h.full i i
  exact M.base_reference_approximation_pivot_cap hd hM hbudget z (g.Q z) hz
    (g.Q_im_nonnegative z hz) B hB (4 * rModel + 1) (pairBall_distance_bound g.graph i i rModel)
    S.diameter_feedback _ _ _ happ S.full_pivot

theorem local_far_deleted_entry_cap
    (h : g.SourceOmegaPlusWithRadii a rModel rError R ell (finiteOmega d) Cq badCount C1 o z)
    (hd : 3 ≤ d) (hz : 0 < z.im) (hmargin : rModel + 1 ≤ R / 8)
    (hfarMargin : rModel + 1 ≤ R / 4 - 1)
    (S : SourceLocalCapBounds d rModel z (g.Q z) B (C1 / Real.log (N : ℝ))
      (C1 * g.sourcePrime a rError z))
    (i j : ((graphBallVertices g.graph o ell)ᶜ : Set (Fin N)))
    (hij : i = j ∨ (outsideGraph g.graph (graphBallVertices g.graph o ell)).Adj i j)
    (hi : i.val ∈ boundaryFarGuard g.graph (graphBallVertices g.graph o ell) (R / 4 - 1)) :
    ‖(g.deficient.delete (graphBallVertices g.graph o ell)).G z i j‖ ≤ commonGreenEntryCap d := by
  let T := graphBallVertices g.graph o ell
  let H := outsideGraph g.graph T
  let M := (g.deficient.delete T).restrict (pairBallVertices H i j rModel)
  have hM : M.graph.Connected := pairBall_connected_of_eq_or_adjacent H i j rModel hij
  have hbudget := g.far_deleted_local_pair_base_budget T rModel (R / 8) (R / 4 - 1)
    hmargin hfarMargin h.structural.1 i j hij ((mem_boundaryFarGuard g.graph T _ i).mp hi)
  have happ : ‖(g.deficient.delete T).G z i j - M.extensionGreen (g.Q z) z
      (pairBallLeft H i j rModel) (pairBallRight H i j rModel)‖ ≤ C1 * g.sourcePrime a rError z := h.deleted i j
  exact (M.base_reference_approximation_entry_cap hd hM hbudget z (g.Q z) hz
    (g.Q_im_nonnegative z hz) (4 * rModel + 1) (pairBall_distance_bound H i j rModel)
    S.diameter_feedback _ _ _ _ happ S.deleted_error S.change).trans (sourceGreenEntryCap_le_common d hd)

theorem local_far_deleted_pivot_cap
    (h : g.SourceOmegaPlusWithRadii a rModel rError R ell (finiteOmega d) Cq badCount C1 o z)
    (hd : 3 ≤ d) (hz : 0 < z.im) (hB : ‖z‖ ≤ B) (hmargin : rModel + 1 ≤ R / 8)
    (hfarMargin : rModel + 1 ≤ R / 4 - 1)
    (S : SourceLocalCapBounds d rModel z (g.Q z) B (C1 / Real.log (N : ℝ))
      (C1 * g.sourcePrime a rError z))
    (i : ((graphBallVertices g.graph o ell)ᶜ : Set (Fin N)))
    (hi : i.val ∈ boundaryFarGuard g.graph (graphBallVertices g.graph o ell) (R / 4 - 1)) :
    ‖((g.deficient.delete (graphBallVertices g.graph o ell)).G z i i)⁻¹‖ ≤ sourceGreenPivotCap d B := by
  let T := graphBallVertices g.graph o ell
  let H := outsideGraph g.graph T
  let M := (g.deficient.delete T).restrict (pairBallVertices H i i rModel)
  have hM : M.graph.Connected := pairBall_connected_of_eq_or_adjacent H i i rModel (Or.inl rfl)
  have hbudget := g.far_deleted_local_pair_base_budget T rModel (R / 8) (R / 4 - 1)
    hmargin hfarMargin h.structural.1 i i (Or.inl rfl) ((mem_boundaryFarGuard g.graph T _ i).mp hi)
  have happ : ‖(g.deficient.delete T).G z i i - M.extensionGreen (g.Q z) z
      (pairBallLeft H i i rModel) (pairBallLeft H i i rModel)‖ ≤ C1 * g.sourcePrime a rError z := h.deleted i i
  exact M.base_reference_approximation_pivot_cap hd hM hbudget z (g.Q z) hz
    (g.Q_im_nonnegative z hz) B hB (4 * rModel + 1) (pairBall_distance_bound H i i rModel)
    S.diameter_feedback _ _ _ happ S.deleted_pivot

end RegularGraph.SourceOmegaPlusWithRadii
end LocalLaw
