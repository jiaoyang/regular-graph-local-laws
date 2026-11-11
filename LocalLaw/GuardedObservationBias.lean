import LocalLaw.FiniteExceptionalBias
import LocalLaw.GuardedBiasParameters
import LocalLaw.SourceObservationTreeValue
import LocalLaw.SourceBiasBadEdges

/-!
# The actual guarded source observation mean

The source mask puts both edge endpoints in the physical deletion guard.
On a good original tree edge the literal observation equals the guarded
cavity minus the scalar tree iterate. A genuine exceptional-edge count
then supplies a good sample and the finite mean comparison.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance guardedObservationBiasDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ}

theorem outsideMatrixCavityValue_guarded_eq (g : RegularGraph N d) (T A : Set (Fin N))
    (hA : A ⊆ Tᶜ) (z : ℂ) (e : OutsideOrientedEdge g.graph T)
    (hsafe : e.val.1 ∈ A ∧ e.val.2 ∈ A) :
    outsideMatrixCavityValue g.graph T (guardedDeletedGreen g.H T A z) e =
      outsideOrientedCavityValue g.graph d T z e := by
  have hentry (i j : (Tᶜ : Set (Fin N))) (hi : i.val ∈ A) (hj : j.val ∈ A) :
      guardedDeletedGreen g.H T A z i.val j.val =
        green (normalizedAdjacency (outsideGraph g.graph T) d) z i j := by
    have hh := guardedDeletedGreen_of_safe g.H T A hA z ⟨i.val, hi⟩ ⟨j.val, hj⟩
    have hmatrix : g.H.submatrix (Subtype.val : (Tᶜ : Set (Fin N)) → Fin N)
        (Subtype.val : (Tᶜ : Set (Fin N)) → Fin N) = normalizedAdjacency (outsideGraph g.graph T) d :=
      (normalizedAdjacency_induce g.graph d Tᶜ).symm
    rw [hmatrix] at hh
    exact hh
  let b : (Tᶜ : Set (Fin N)) := ⟨e.val.1, e.property.2.1⟩
  let c : (Tᶜ : Set (Fin N)) := ⟨e.val.2, e.property.2.2⟩
  unfold outsideMatrixCavityValue outsideOrientedCavityValue matrixCavityTerm
  rw [hentry c c hsafe.2 hsafe.2, hentry c b hsafe.2 hsafe.1,
    hentry b c hsafe.1 hsafe.2, hentry b b hsafe.1 hsafe.1]

theorem sourceObservation_good_guarded_identity (g : RegularGraph N d) (hd : 3 ≤ d)
    (T : Set (Fin N)) (R r : ℕ) (hmargin : r + 2 ≤ R / 4)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (e : OutsideOrientedEdge g.graph T) (he : e ∉ sourceBiasBadEdges g.graph T r (R / 4)) :
    g.sourceSingletonObservation T r (R / 4) z q e =
      outsideMatrixCavityValue g.graph T
        (guardedDeletedGreen g.H T (boundaryFarGuard g.graph T (R / 4 - 1)) z) e -
        cavityIterate z q (r + 1) := by
  obtain ⟨hfar, htree⟩ := not_mem_sourceBiasBadEdges g.graph T r (R / 4) e he
  have hsafe := source_far_edge_guard g.graph T R (by omega) e hfar
  rw [g.outsideMatrixCavityValue_guarded_eq T (boundaryFarGuard g.graph T (R / 4 - 1))
    (boundaryFarGuard_subset_complement g.graph T _) z e hsafe]
  exact g.sourceSingletonObservation_eq_on_good_edge hd T r (R / 4) hmargin z q hz hq e htree hfar

/-- The actual finite one-edge observation mean, with existence of a good
sample proved from its actual exceptional-edge count. -/
theorem source_observation_bias_of_caps (g : RegularGraph N d) (hd : 3 ≤ d)
    (T : Set (Fin N)) (R r : ℕ) (hmargin : r + 2 ≤ R / 4)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (C L bZ δ : ℝ) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (caps : g.GuardedDeletionCaps T (boundaryFarGuard g.graph T (R / 4 - 1)) z C L)
    (hZ : ∀ e, ‖g.sourceSingletonObservation T r (R / 4) z q e‖ ≤ bZ)
    (hcount : (sourceBiasBadEdges g.graph T r (R / 4)).card < Fintype.card (OutsideOrientedEdge g.graph T))
    (hQ : ‖finiteComplexMean (outsideMatrixCavityValue g.graph T
      (guardedDeletedGreen g.H T (boundaryFarGuard g.graph T (R / 4 - 1)) z)) - g.Q z‖ ≤ δ) :
    ‖finiteComplexMean (g.sourceSingletonObservation T r (R / 4) z q) -
      (g.Q z - cavityIterate z q (r + 1))‖ ≤
      (Fintype.card (OutsideOrientedEdge g.graph T) : ℝ)⁻¹ *
        ((sourceBiasBadEdges g.graph T r (R / 4)).card : ℝ) *
          (2 * (C + C ^ 2 * L + bZ)) + δ := by
  let E := OutsideOrientedEdge g.graph T
  let bad := sourceBiasBadEdges g.graph T r (R / 4)
  let p : E → Prop := fun e => e ∉ bad
  let f := outsideMatrixCavityValue g.graph T
    (guardedDeletedGreen g.H T (boundaryFarGuard g.graph T (R / 4 - 1)) z)
  obtain ⟨e, _, he⟩ := Finset.exists_mem_not_mem_of_card_lt_card
    (show bad.card < (Finset.univ : Finset E).card by simpa only [Finset.card_univ] using hcount)
  letI : Nonempty E := ⟨e⟩
  have hcap : ∀ e, ‖f e‖ ≤ C + C ^ 2 * L :=
    outsideMatrixCavityValue_norm_bound g.graph T _ C L hC hL caps.guarded_diagonal caps.guarded_edge caps.guarded_pivot
  have hgood : ∀ e, p e → g.sourceSingletonObservation T r (R / 4) z q e = f e - cavityIterate z q (r + 1) :=
    fun e he => g.sourceObservation_good_guarded_identity hd T R r hmargin q z hz hq e he
  have hh := finiteComplexMean_cavity_bias p (g.sourceSingletonObservation T r (R / 4) z q) f
    (cavityIterate z q (r + 1)) (g.Q z) bZ (C + C ^ 2 * L) δ hZ hcap hgood ⟨e, he⟩ hQ
  have hbad : Nat.card {e : E // ¬p e} = bad.card := by
    simp only [p, not_not, Nat.card_eq_fintype_card, Fintype.card_subtype]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [hbad] at hh
  exact hh

end RegularGraph
end LocalLaw
