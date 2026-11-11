import LocalLaw.ActualGuardedGreenCaps
import LocalLaw.GuardedBiasParameters

/-! # Actual source caps supply the guarded deletion-Ward interface

The principal minor is identified with the physical deficient deleted Green
matrix. Deleted diagonal/edge/pivot caps are used only on the proved far
guard. The guarded matrix uses the original Green matrix elsewhere, and its
nonzero diagonal follows from the genuine Hermitian resolvent theorem.
-/

noncomputable section
namespace LocalLaw

local instance actualGuardedDeletionCapsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

namespace RegularGraph
variable {N d : ℕ}

theorem deletedGreen_eq_principalGreen (g : RegularGraph N d) (T : Set (Fin N)) (z : ℂ) :
    (g.deficient.delete T).G z =
      green (g.H.submatrix (Subtype.val : (Tᶜ : Set (Fin N)) → Fin N)
        (Subtype.val : (Tᶜ : Set (Fin N)) → Fin N)) z := by
  change green (normalizedAdjacency (g.graph.induce Tᶜ) d) z = _
  rw [normalizedAdjacency_induce]
  rfl

end RegularGraph

namespace ActualGuardedGreenCaps
variable {N d ell R : ℕ} {g : RegularGraph N d} {o : Fin N} {z : ℂ} {C L : ℝ}

theorem to_guardedDeletionCaps (caps : ActualGuardedGreenCaps g o ell R z C L) (hz : 0 < z.im) :
    g.GuardedDeletionCaps (graphBallVertices g.graph o ell)
      (boundaryFarGuard g.graph (graphBallVertices g.graph o ell) (R / 4 - 1)) z C L := by
  let T := graphBallVertices g.graph o ell
  let A := boundaryFarGuard g.graph T (R / 4 - 1)
  have hA : A ⊆ Tᶜ := boundaryFarGuard_subset_complement g.graph T _
  have hSd : ∀ i : A, ‖green (g.H.submatrix (Subtype.val : (Tᶜ : Set (Fin N)) → Fin N)
      (Subtype.val : (Tᶜ : Set (Fin N)) → Fin N)) z ⟨i.val, hA i.property⟩ ⟨i.val, hA i.property⟩‖ ≤ C := by
    intro i
    rw [← g.deletedGreen_eq_principalGreen T z]
    exact caps.deleted_diag ⟨i.val, hA i.property⟩ i.property
  have hSe : ∀ i j : A, g.graph.Adj i.val j.val →
      ‖green (g.H.submatrix (Subtype.val : (Tᶜ : Set (Fin N)) → Fin N)
        (Subtype.val : (Tᶜ : Set (Fin N)) → Fin N)) z ⟨i.val, hA i.property⟩ ⟨j.val, hA j.property⟩‖ ≤ C := by
    intro i j hij
    rw [← g.deletedGreen_eq_principalGreen T z]
    exact caps.deleted_adj ⟨i.val, hA i.property⟩ ⟨j.val, hA j.property⟩ i.property hij
  have hSi : ∀ i : A, ‖(green (g.H.submatrix (Subtype.val : (Tᶜ : Set (Fin N)) → Fin N)
      (Subtype.val : (Tᶜ : Set (Fin N)) → Fin N)) z ⟨i.val, hA i.property⟩ ⟨i.val, hA i.property⟩)⁻¹‖ ≤ L := by
    intro i
    rw [← g.deletedGreen_eq_principalGreen T z]
    exact caps.deleted_pivot ⟨i.val, hA i.property⟩ i.property
  obtain ⟨hguardD, hguardE, hguardP, hguardI⟩ := guardedDeletedGreen_local_caps g.graph g.H
    (normalizedAdjacency_isHermitian g.graph d) T A hA z hz C L
    caps.full_diag caps.full_adj caps.full_pivot hSd hSe hSi
  exact ⟨caps.full_diag, caps.full_adj, caps.full_pivot, hguardD, hguardE, hguardP, hguardI, caps.boundary⟩

end ActualGuardedGreenCaps

theorem eventually_actualGuardedDeletionCaps (a b d : ℕ) (c β C1 B : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hc : 0 < c)
    (hβ : 0 < β) (hβc : β ≤ c / 32) (hC1 : 0 ≤ C1) (hB : 0 ≤ B) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0 < z.im → ‖z‖ ≤ B → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
      ∀ Cq badCount : ℕ,
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c / 4) d N) (actualCavityDepth a d N z - 1)
        (finiteOmega d) Cq badCount C1 o z →
      let T := graphBallVertices g.graph o (actualCavityDepth a d N z - 1)
      g.GuardedDeletionCaps T (boundaryFarGuard g.graph T (logarithmicRadius (c / 4) d N / 4 - 1)) z
        (guardedGreenEntryCap d) (sourceGreenPivotCap d B) := by
  filter_upwards [eventually_actualGuardedGreenCaps a b d c β C1 B ha hb hd hc hβ hβc hC1 hB] with N hcaps
  intro g o z hz hzB hscale Cq badCount hplus
  exact (hcaps g o z hz hzB hscale Cq badCount hplus).to_guardedDeletionCaps hz

end LocalLaw
