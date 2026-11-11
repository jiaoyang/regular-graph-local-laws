import LocalLaw.SourceGuardedCapParameters
import LocalLaw.BoundaryDeletedCaps
import LocalLaw.EffectiveModelRadius

/-! # Realized physical caps for the guarded source Q comparison

All full diagonal/edge pivots, far-boundary deleted pivots, and the actual
outer-boundary deleted matrix have derived degree/domain constants. Every
feedback and approximation smallness condition is realized at the effective
model radius and nominal paper error, including beta=c/32.
-/

noncomputable section
set_option maxHeartbeats 2200000
namespace LocalLaw

local instance actualGuardedGreenCapsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def guardedGreenEntryCap (d : ℕ) : ℝ := 2 * commonGreenEntryCap d

structure ActualGuardedGreenCaps {N d : ℕ} (g : RegularGraph N d)
    (o : Fin N) (ell R : ℕ) (z : ℂ) (C L : ℝ) : Prop where
  full_diag : ∀ i, ‖g.G z i i‖ ≤ C
  full_adj : ∀ i j, g.graph.Adj i j → ‖g.G z i j‖ ≤ C
  full_pivot : ∀ i, ‖(g.G z i i)⁻¹‖ ≤ L
  deleted_diag : let T := graphBallVertices g.graph o ell
    ∀ i : (Tᶜ : Set (Fin N)), i.val ∈ boundaryFarGuard g.graph T (R / 4 - 1) →
      ‖(g.deficient.delete T).G z i i‖ ≤ C
  deleted_adj : let T := graphBallVertices g.graph o ell
    ∀ i j : (Tᶜ : Set (Fin N)), i.val ∈ boundaryFarGuard g.graph T (R / 4 - 1) →
      (outsideGraph g.graph T).Adj i j → ‖(g.deficient.delete T).G z i j‖ ≤ C
  deleted_pivot : let T := graphBallVertices g.graph o ell
    ∀ i : (Tᶜ : Set (Fin N)), i.val ∈ boundaryFarGuard g.graph T (R / 4 - 1) →
      ‖((g.deficient.delete T).G z i i)⁻¹‖ ≤ L
  boundary : let T := graphBallVertices g.graph o ell
    ∀ i j : (Tᶜ : Set (Fin N)),
      (∃ t : T, g.graph.Adj t.val i.val) → (∃ t : T, g.graph.Adj t.val j.val) →
      ‖(g.deficient.delete T).G z i j‖ ≤ C

theorem eventually_actualGuardedGreenCaps (a b d : ℕ) (c β C1 B : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hc : 0 < c)
    (hβ : 0 < β) (hβc : β ≤ c / 32) (hC1 : 0 ≤ C1) (hB : 0 ≤ B) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0 < z.im → ‖z‖ ≤ B → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
      ∀ Cq badCount : ℕ,
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c / 4) d N) (actualCavityDepth a d N z - 1)
        (finiteOmega d) Cq badCount C1 o z →
      ActualGuardedGreenCaps g o (actualCavityDepth a d N z - 1) (logarithmicRadius (c / 4) d N) z
        (guardedGreenEntryCap d) (sourceGreenPivotCap d B) := by
  have ha0 : 0 < a := by omega
  have hdepth := (lowerLogLogRadius_tendsto a d ha0 hd).eventually (Filter.eventually_ge_atTop 4)
  filter_upwards [eventually_sourceLocalCapBounds a b d β C1 B ha hb hd hβ hC1 hB,
    eventually_source_radius_hierarchy a d c β hd hc hβ hβc, hdepth] with
      N hscalar hradii hdepth
  intro g o z hz hzB hscale Cq badCount hplus
  let r := effectiveModelRadius a d N β
  let rn := logarithmicRadius β d N
  let R := logarithmicRadius (c / 4) d N
  let ell := actualCavityDepth a d N z - 1
  have hell : ell ≤ doubleLogRadius a d N := (actualCavityDepth_radius_bounds a d N z hdepth).2
  have hnom : r ≤ rn := Nat.sub_le _ _
  have hboundaryMargin : r + 2 * ell + 2 ≤ R / 8 := by
    have h₁ := hradii.1
    have h₂ := hradii.2.1
    dsimp only [r, rn, R, ell] at *
    unfold effectiveModelRadius modelRadiusLoss
    omega
  have hlocalMargin : r + 1 ≤ R / 8 := by omega
  have hfarMargin : r + 1 ≤ R / 4 - 1 := by
    have h₁ := hradii.2.1
    have h₂ := hradii.2.2.1
    dsimp only [rn, R] at *
    omega
  obtain ⟨S, hextra⟩ := hscalar z (g.Q z) hz hscale r hnom hplus.cavity
  have S' : SourceLocalCapBounds d r z (g.Q z) B (C1 / Real.log (N : ℝ))
      (C1 * g.sourcePrime a rn z) := S
  have hentry : commonGreenEntryCap d ≤ guardedGreenEntryCap d := by
    have hC := finiteExtraReferenceConstant_ge_one d hd
    simp only [commonGreenEntryCap, guardedGreenEntryCap]
    linarith
  have hboundary : boundaryDeletedEntryCap d ≤ guardedGreenEntryCap d := by
    unfold boundaryDeletedEntryCap guardedGreenEntryCap commonGreenEntryCap
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (hplus.local_full_entry_cap hd hz hlocalMargin S' i i (Or.inl rfl)).trans hentry
  · intro i j hij
    exact (hplus.local_full_entry_cap hd hz hlocalMargin S' i j (Or.inr hij)).trans hentry
  · exact hplus.local_full_pivot_cap hd hz hzB hlocalMargin S'
  · dsimp only
    intro i hi
    exact (hplus.local_far_deleted_entry_cap hd hz hlocalMargin hfarMargin S' i i (Or.inl rfl) hi).trans hentry
  · dsimp only
    intro i j hi hij
    exact (hplus.local_far_deleted_entry_cap hd hz hlocalMargin hfarMargin S' i j (Or.inr hij) hi).trans hentry
  · exact hplus.local_far_deleted_pivot_cap hd hz hzB hlocalMargin hfarMargin S'
  · dsimp only
    intro i j hi hj
    exact (hplus.outer_boundary_deleted_entry_cap hd hz hboundaryMargin S'.deleted_error hextra i j hi hj).trans hboundary

end LocalLaw
