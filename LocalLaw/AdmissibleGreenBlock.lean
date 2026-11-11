import LocalLaw.AdmissibleSampleGeometry
import LocalLaw.SourceGuardedCaps
import LocalLaw.BoundaryPivot

/-! # The actual deleted Green block at admissible sampled roots

Only the two-root local models are asserted to vanish off the diagonal.
The larger endpoint/target union model is not identified with this diagonal
matrix. Source deleted approximation therefore gives an actual entrywise
diagonal approximation, and the tested far geometry supplies base-class
diagonal model pivots.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000
namespace LocalLaw

local instance admissibleGreenBlockDecidable (p : Prop) : Decidable p := Classical.propDecidable p

namespace RegularGraph
variable {N d : ℕ} {ι : Type*} [Fintype ι]

def admissibleState (g : RegularGraph N d) (T : Set (Fin N))
    (boundary : ι ≃ BoundaryOrientedEdge g.graph T) (S : LocalSamplingFiber g.graph T) :
    LabelledResamplingState (Fin N) T ι := ⟨g.graph, boundary, S⟩

def admissibleDeletedGreenBlock (g : RegularGraph N d) (T : Set (Fin N))
    (boundary : ι ≃ BoundaryOrientedEdge g.graph T) (S : LocalSamplingFiber g.graph T)
    (selector : ℕ) (z : ℂ) :
    Matrix ((g.admissibleState T boundary S).AdmissibleSampleIndex selector)
      ((g.admissibleState T boundary S).AdmissibleSampleIndex selector) ℂ := fun i j =>
  (g.deficient.delete T).G z ((g.admissibleState T boundary S).admissibleSampleVertex selector i)
    ((g.admissibleState T boundary S).admissibleSampleVertex selector j)

def admissibleDiagonalEntry (g : RegularGraph N d) (T : Set (Fin N))
    (boundary : ι ≃ BoundaryOrientedEdge g.graph T) (S : LocalSamplingFiber g.graph T)
    (selector r : ℕ) (z q : ℂ)
    (i : (g.admissibleState T boundary S).AdmissibleSampleIndex selector) : ℂ :=
  let b := (g.admissibleState T boundary S).admissibleSampleVertex selector i
  g.deletedP T r z q b b

def admissibleDiagonalBlock (g : RegularGraph N d) (T : Set (Fin N))
    (boundary : ι ≃ BoundaryOrientedEdge g.graph T) (S : LocalSamplingFiber g.graph T)
    (selector r : ℕ) (z q : ℂ) :
    Matrix ((g.admissibleState T boundary S).AdmissibleSampleIndex selector)
      ((g.admissibleState T boundary S).AdmissibleSampleIndex selector) ℂ :=
  Matrix.diagonal (g.admissibleDiagonalEntry T boundary S selector r z q)

omit [Fintype ι] in
theorem admissible_pair_model_zero (g : RegularGraph N d) (T : Set (Fin N))
    (boundary : ι ≃ BoundaryOrientedEdge g.graph T) (S : LocalSamplingFiber g.graph T)
    (selector r : ℕ) (hsep : 2 * r + 1 ≤ selector) (hd : 3 ≤ d)
    (z q : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (i j : (g.admissibleState T boundary S).AdmissibleSampleIndex selector) (hij : i ≠ j) :
    g.deletedP T r z q
      ((g.admissibleState T boundary S).admissibleSampleVertex selector i)
      ((g.admissibleState T boundary S).admissibleSampleVertex selector j) = 0 := by
  let s := g.admissibleState T boundary S
  exact (g.deficient.delete T).pair_restriction_cross_zero hd _ _ r q z hz hq
    (s.admissibleSamplePair_disconnected selector r hsep i j hij)

omit [Fintype ι] in
theorem admissibleDiagonalEntry_ne_zero (g : RegularGraph N d) (T : Set (Fin N))
    (boundary : ι ≃ BoundaryOrientedEdge g.graph T) (S : LocalSamplingFiber g.graph T)
    (selector r : ℕ) (hd : 3 ≤ d) (z q : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (i : (g.admissibleState T boundary S).AdmissibleSampleIndex selector) :
    g.admissibleDiagonalEntry T boundary S selector r z q i ≠ 0 := by
  let b := (g.admissibleState T boundary S).admissibleSampleVertex selector i
  let M := (g.deficient.delete T).restrict (pairBallVertices (outsideGraph g.graph T) b b r)
  exact M.extensionGreen_diagonal_ne_zero hd q z hz hq (pairBallLeft (outsideGraph g.graph T) b b r)

end RegularGraph

namespace RegularGraph.SourceOmegaPlusWithRadii
variable {N d a rModel rError R ell Cq badCount : ℕ} {C1 B : ℝ} {o : Fin N} {z : ℂ}
variable {g : RegularGraph N d} {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem admissible_block_diagonal_approximation
    (h : g.SourceOmegaPlusWithRadii a rModel rError R ell (finiteOmega d) Cq badCount C1 o z)
    (hd : 3 ≤ d) (hz : 0 < z.im)
    (boundary : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
    (S : LocalSamplingFiber g.graph (graphBallVertices g.graph o ell))
    (selector : ℕ) (hsep : 2 * rModel + 1 ≤ selector) :
    ∀ i j, ‖g.admissibleDeletedGreenBlock (graphBallVertices g.graph o ell) boundary S selector z i j -
      g.admissibleDiagonalBlock (graphBallVertices g.graph o ell) boundary S selector rModel z (g.Q z) i j‖ ≤
        C1 * g.sourcePrime a rError z := by
  intro i j
  by_cases hij : i = j
  · subst j
    simp only [admissibleDeletedGreenBlock, admissibleDiagonalBlock, Matrix.diagonal_apply_eq,
      admissibleDiagonalEntry]
    exact h.deleted _ _
  · have hzero := g.admissible_pair_model_zero (graphBallVertices g.graph o ell) boundary S selector rModel
      hsep hd z (g.Q z) hz (g.Q_im_nonnegative z hz) i j hij
    have happ := h.deleted
      ((g.admissibleState (graphBallVertices g.graph o ell) boundary S).admissibleSampleVertex selector i)
      ((g.admissibleState (graphBallVertices g.graph o ell) boundary S).admissibleSampleVertex selector j)
    rw [hzero, sub_zero] at happ
    simpa only [admissibleDeletedGreenBlock, admissibleDiagonalBlock, Matrix.diagonal_apply_ne _ hij, sub_zero] using happ

omit [Fintype ι] in
theorem admissible_diagonal_model_pivot_cap
    (h : g.SourceOmegaPlusWithRadii a rModel rError R ell (finiteOmega d) Cq badCount C1 o z)
    (hd : 3 ≤ d) (hz : 0 < z.im) (hB : ‖z‖ ≤ B) (hC1 : 0 ≤ C1) (hlog : 0 ≤ Real.log (N : ℝ))
    (hmargin : rModel + 1 ≤ R / 8)
    (boundary : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
    (S : LocalSamplingFiber g.graph (graphBallVertices g.graph o ell))
    (selector : ℕ) (hsep : rModel + 1 ≤ selector)
    (Scap : SourceLocalCapBounds d rModel z (g.Q z) B (C1 / Real.log (N : ℝ))
      (C1 * g.sourcePrime a rError z)) :
    ∀ i, ‖(g.admissibleDiagonalEntry (graphBallVertices g.graph o ell) boundary S selector rModel z (g.Q z) i)⁻¹‖ ≤
      sourceGreenPivotCap d B := by
  intro i
  let T := graphBallVertices g.graph o ell
  let s := g.admissibleState T boundary S
  let b := s.admissibleSampleVertex selector i
  let H := outsideGraph g.graph T
  let M := (g.deficient.delete T).restrict (pairBallVertices H b b rModel)
  have hM : M.graph.Connected := pairBall_connected_of_eq_or_adjacent H b b rModel (Or.inl rfl)
  have hbudget := g.far_deleted_local_pair_base_budget T rModel (R / 8) selector hmargin hsep
    h.structural.1 b b (Or.inl rfl) (s.admissibleSampleVertex_far_boundary selector i)
  have herror : 0 + pairSensitivityConstant d * ‖g.Q z - semicircleRoot z‖ ≤
      1 / (2 * finiteReferenceConstant d * (B + 2)) :=
    (add_le_add_right (div_nonneg hC1 hlog) _).trans Scap.full_pivot
  change ‖(M.extensionGreen (g.Q z) z (pairBallLeft H b b rModel) (pairBallLeft H b b rModel))⁻¹‖ ≤ _
  exact M.base_reference_approximation_pivot_cap hd hM hbudget z (g.Q z) hz
    (g.Q_im_nonnegative z hz) B hB (4 * rModel + 1) (pairBall_distance_bound H b b rModel)
    Scap.diameter_feedback (pairBallLeft H b b rModel)
    (M.extensionGreen (g.Q z) z (pairBallLeft H b b rModel) (pairBallLeft H b b rModel)) 0 (by simp) herror

end RegularGraph.SourceOmegaPlusWithRadii
end LocalLaw
