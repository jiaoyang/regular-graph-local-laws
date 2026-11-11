import LocalLaw.LocalExcessGeometry

/-!
# Actual boundary labels in multiply attached annulus components

A direct finite injection into bad-component fibers turns the cutset excess
sum into an actual bad-label count. Every other label has exactly one
attachment in its original annulus component.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance annulusBadLabelsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*} [Fintype V]

def multiattachmentBoundaryLabels (G : SimpleGraph V) (o : V) {ell R : ℕ} (h : ell + 1 ≤ R) :
    Finset (BoundaryOrientedEdge G (graphBallVertices G o ell)) :=
  Finset.univ.filter (fun a => 2 ≤ Nat.card (AmbientBallBoundaryFiber G o h (ambientBoundaryComponent G o h a)))

/-- Actual bad boundary-label count, derived from annulus excess. -/
theorem multiattachmentBoundaryLabels_card (G : SimpleGraph V) (o : V) {ell R ω : ℕ}
    (h : ell + 1 ≤ R) (hbudget : graphBallExcess G o R ≤ ω) :
    (multiattachmentBoundaryLabels G o h).card ≤ 2 * ω := by
  let Bad := fun C : BallAnnulusComponent G o ell R => 2 ≤ Nat.card (AmbientBallBoundaryFiber G o h C)
  let enc : (multiattachmentBoundaryLabels G o h) →
      Σ C : {C : BallAnnulusComponent G o ell R // Bad C}, AmbientBallBoundaryFiber G o h C.val :=
    fun a => ⟨⟨ambientBoundaryComponent G o h a.val, (Finset.mem_filter.mp a.property).2⟩, ⟨a.val, rfl⟩⟩
  have hinj : Function.Injective enc := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun p : Σ C : {C : BallAnnulusComponent G o ell R // Bad C},
      AmbientBallBoundaryFiber G o h C.val => p.2.val) hab
  have hcard := Nat.card_le_card_of_injective enc hinj
  rw [Nat.card_sigma] at hcard
  have hsum : (∑ C : {C : BallAnnulusComponent G o ell R // Bad C}, Nat.card (AmbientBallBoundaryFiber G o h C.val)) =
      ∑ C ∈ (Finset.univ : Finset (BallAnnulusComponent G o ell R)).filter Bad,
        Nat.card (AmbientBallBoundaryFiber G o h C) := by
    symm
    exact Finset.sum_subtype _ (by simp) _
  rw [hsum] at hcard
  have hbound := ball_multiple_attachment_sum_bound G o (show ell ≤ R by omega) hbudget
  have hbound' : (∑ C ∈ (Finset.univ : Finset (BallAnnulusComponent G o ell R)).filter Bad,
      Nat.card (AmbientBallBoundaryFiber G o h C)) ≤ 2 * ω := by
    simpa only [Bad, ambientBallBoundaryFiber_card] using hbound
  have hcard' : (multiattachmentBoundaryLabels G o h).card ≤
      ∑ C ∈ (Finset.univ : Finset (BallAnnulusComponent G o ell R)).filter Bad,
        Nat.card (AmbientBallBoundaryFiber G o h C) := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using hcard
  exact hcard'.trans hbound'

/-- A label outside the bad set has exactly one original annulus attachment. -/
theorem ambientBoundaryFiber_card_one_of_not_bad (G : SimpleGraph V) (o : V) {ell R : ℕ}
    (h : ell + 1 ≤ R) (a : BoundaryOrientedEdge G (graphBallVertices G o ell))
    (ha : a ∉ multiattachmentBoundaryLabels G o h) :
    Nat.card (AmbientBallBoundaryFiber G o h (ambientBoundaryComponent G o h a)) = 1 := by
  have hlt : ¬2 ≤ Nat.card (AmbientBallBoundaryFiber G o h (ambientBoundaryComponent G o h a)) := by
    intro hh
    exact ha (Finset.mem_filter.mpr ⟨Finset.mem_univ a, hh⟩)
  have hnonempty : Nonempty (AmbientBallBoundaryFiber G o h (ambientBoundaryComponent G o h a)) :=
    ⟨⟨a, rfl⟩⟩
  have hfinite : Finite (AmbientBallBoundaryFiber G o h (ambientBoundaryComponent G o h a)) := inferInstance
  have hpos := Nat.card_pos_iff.mpr ⟨hnonempty, hfinite⟩
  omega

end LocalLaw
