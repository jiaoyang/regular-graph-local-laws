import LocalLaw.PairModelFarZero
import LocalLaw.NearDiagonalInverse
import LocalLaw.EmbeddedDeletionComparison
import LocalLaw.SourceEndpointVertices
import LocalLaw.ActualGuardedDeletionCaps

/-!
# The genuine Green block on the selected sampled first vertices

The J-test gives an injective selected-vertex map. The physical block is
invertible by principal resolvent deletion. Distinct pair-local models are
exactly zero, so a source approximation bounds its actual off-diagonal
entries. A small aggregate error then bounds true inverse row sums.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1600000
namespace LocalLaw
local instance selectedFirstGreenDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace LabelledResamplingState
variable {V : Type} {T : Set V} {ι : Type} [Fintype ι]

omit [Fintype ι] in
theorem selectedFirst_far (s : LabelledResamplingState V T ι) (selector : ℕ)
    (i j : s.AdmissibleSampleIndex selector) (hij : i ≠ j) :
    (selector : ℕ∞) < (outsideGraph s.graph T).edist
      (s.admissibleSampleVertex selector i) (s.admissibleSampleVertex selector j) := by
  have hne : s.boundary j.val ≠ s.boundary i.val := by
    intro h
    exact hij (Subtype.ext (s.boundary.injective h).symm)
  exact i.property.2 (s.boundary j.val) hne
    (s.admissibleSampleVertex selector i) (Or.inr (Or.inl rfl))
    (s.admissibleSampleVertex selector j) (Or.inr (Or.inl rfl))

omit [Fintype ι] in
def selectedFirstEmbedding (s : LabelledResamplingState V T ι) (selector : ℕ) :
    s.AdmissibleSampleIndex selector ↪ (Tᶜ : Set V) where
  toFun := s.admissibleSampleVertex selector
  inj' := by
    intro i j h
    by_contra hij
    have hh := s.selectedFirst_far selector i j hij
    rw [h, SimpleGraph.edist_self] at hh
    exact (not_lt_of_ge (bot_le : (0 : ℕ∞) ≤ (selector : ℕ∞))) hh

variable [Fintype V] [DecidableEq V]

def selectedFirstGreen (s : LabelledResamplingState V T ι) (selector d : ℕ) (z : ℂ) :=
  (green (normalizedAdjacency (outsideGraph s.graph T) d) z).submatrix
    (s.selectedFirstEmbedding selector) (s.selectedFirstEmbedding selector)

omit [Fintype V] [DecidableEq V] [Fintype ι] in
theorem selectedFirst_mem_old_guard (s : LabelledResamplingState V T ι) (selector : ℕ)
    (hselector : 1 ≤ selector) (i : s.AdmissibleSampleIndex selector) :
    (s.admissibleSampleVertex selector i).val ∈ boundaryFarGuard s.graph T (selector - 1) := by
  have hfar := s.admissibleSampleVertex_far_boundary selector i
  have hdiv : (4 * selector) / 4 = selector := by omega
  have hsafe := source_far_edge_guard s.graph T (4 * selector) (by omega)
    (s.samples (s.boundary i.val)) (by simpa only [hdiv] using hfar)
  simpa only [hdiv] using hsafe.1

theorem selectedFirstGreen_isUnit (s : LabelledResamplingState V T ι) (selector d : ℕ)
    (z : ℂ) (hz : 0 < z.im) : IsUnit (s.selectedFirstGreen selector d z) := by
  let I := s.AdmissibleSampleIndex selector
  let e := s.selectedFirstEmbedding selector
  letI : DecidablePred (fun i : I => i ∈ (Set.univ : Set I)) := fun _ => Classical.propDecidable _
  letI : Fintype (Set.univ : Set I) := Subtype.fintype _
  let φ : I ≃ (Set.univ : Set I) :=
    { toFun := fun i => ⟨i, trivial⟩
      invFun := Subtype.val
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hh := embedded_green_retained_isUnit (normalizedAdjacency (outsideGraph s.graph T) d)
    (normalizedAdjacency_isHermitian _ _) z hz e (Set.univ : Set I)
  have h := (Matrix.isUnit_submatrix_equiv φ φ).mpr hh
  exact h

theorem selectedFirstGreen_inverse_rows (s : LabelledResamplingState V T ι) (selector d : ℕ)
    (z : ℂ) (hz : 0 < z.im) (P δ : ℝ) (hP : 0 ≤ P) (hδ : 0 ≤ δ)
    (hpivot : ∀ i : s.AdmissibleSampleIndex selector,
      ‖((s.selectedFirstGreen selector d z) i i)⁻¹‖ ≤ P)
    (hoff : ∀ i j : s.AdmissibleSampleIndex selector, i ≠ j →
      ‖s.selectedFirstGreen selector d z i j‖ ≤ δ)
    (small : P * (Fintype.card (s.AdmissibleSampleIndex selector) : ℝ) * δ ≤ 1 / 2) :
    ∀ i, ∑ j, ‖(s.selectedFirstGreen selector d z)⁻¹ i j‖ ≤ 2 * P := by
  let A := s.selectedFirstGreen selector d z
  have hdiag : ∀ i, A i i ≠ 0 := fun i =>
    green_diagonal_ne_zero _ (normalizedAdjacency_isHermitian _ _) z hz (s.selectedFirstEmbedding selector i)
  have hE : ∀ i, ∑ j, ‖(A - Matrix.diagonal (fun k => A k k)) i j‖ ≤
      (Fintype.card (s.AdmissibleSampleIndex selector) : ℝ) * δ := by
    intro i
    calc
      _ ≤ ∑ _j : s.AdmissibleSampleIndex selector, δ := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hij : i = j
        · subst j
          simpa only [Matrix.sub_apply, Matrix.diagonal_apply_eq, sub_self, norm_zero] using hδ
        · simpa only [Matrix.sub_apply, Matrix.diagonal_apply_ne _ hij, sub_zero] using hoff i j hij
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact inverse_rows_of_small_offdiagonal A (s.selectedFirstGreen_isUnit selector d z hz) P
    ((Fintype.card (s.AdmissibleSampleIndex selector) : ℝ) * δ) hP (by positivity) hdiag hpivot hE
      (by nlinarith only [small])

end LabelledResamplingState

namespace RegularGraph
variable {N d : ℕ} {ι : Type} [Fintype ι]

omit [Fintype ι] in
theorem selectedFirstGreen_pivot_of_guardedCaps (g : RegularGraph N d) (T : Set (Fin N))
    (boundary : ι ≃ BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T)
    (selector : ℕ) (hselector : 1 ≤ selector) (z : ℂ) (C P : ℝ)
    (caps : g.GuardedDeletionCaps T (boundaryFarGuard g.graph T (selector - 1)) z C P) :
    let s := g.admissibleState T boundary samples
    ∀ i : s.AdmissibleSampleIndex selector, ‖(s.selectedFirstGreen selector d z i i)⁻¹‖ ≤ P := by
  dsimp only
  let s := g.admissibleState T boundary samples
  let A := boundaryFarGuard g.graph T (selector - 1)
  intro i
  let b := s.admissibleSampleVertex selector i
  have hb : b.val ∈ A := s.selectedFirst_mem_old_guard selector hselector i
  have hh := guardedDeletedGreen_of_safe g.H T A (boundaryFarGuard_subset_complement g.graph T _)
    z ⟨b.val, hb⟩ ⟨b.val, hb⟩
  have hmatrix : g.H.submatrix (Subtype.val : (Tᶜ : Set (Fin N)) → Fin N)
      (Subtype.val : (Tᶜ : Set (Fin N)) → Fin N) = normalizedAdjacency (outsideGraph g.graph T) d :=
    (normalizedAdjacency_induce g.graph d Tᶜ).symm
  rw [hmatrix] at hh
  change guardedDeletedGreen g.H T A z b.val b.val = green
    (normalizedAdjacency (outsideGraph g.graph T) d) z b b at hh
  have hp := caps.guarded_pivot b.val
  change ‖(guardedDeletedGreen g.H T A z b.val b.val)⁻¹‖ ≤ P at hp
  rw [hh] at hp
  exact hp

omit [Fintype ι] in
theorem selectedFirstGreen_offdiagonal_of_pair_approximation (g : RegularGraph N d) (hd : 3 ≤ d)
    (T : Set (Fin N)) (boundary : ι ≃ BoundaryOrientedEdge g.graph T)
    (samples : LocalSamplingFiber g.graph T) (selector r : ℕ) (hsep : 2 * r + 1 ≤ selector)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) (δ : ℝ)
    (happrox : ∀ x y, ‖(g.deficient.delete T).G z x y - (g.deficient.delete T).P r z q x y‖ ≤ δ) :
    let s := g.admissibleState T boundary samples
    ∀ i j : s.AdmissibleSampleIndex selector, i ≠ j → ‖s.selectedFirstGreen selector d z i j‖ ≤ δ := by
  dsimp only
  let s := g.admissibleState T boundary samples
  intro i j hij
  have hfar := (ENat.coe_le_coe.mpr hsep).trans_lt (s.selectedFirst_far selector i j hij)
  have hzero := (g.deficient.delete T).P_eq_zero_of_edist_gt hd r q z hz hq
    (s.admissibleSampleVertex selector i) (s.admissibleSampleVertex selector j) hfar
  have hh := happrox (s.admissibleSampleVertex selector i) (s.admissibleSampleVertex selector j)
  rw [hzero, sub_zero] at hh
  exact hh

end RegularGraph
end LocalLaw
