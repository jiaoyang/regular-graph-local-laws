import LocalLaw.AnnulusBadLabels
import LocalLaw.CentralEndpointCharges

/-!
# Unique actual central attachment outside the deterministic bad set

The ambient annulus bad-label count is at most twice the excess. Every
remaining label is the only attachment of its actual central component,
whose inherited deleted-model deficit sum is therefore exactly one.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance centralUniqueAttachmentDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance (priority := high) canonicalCentralUniqueAttachmentMemDecidable
    {A : Type*} (H : SimpleGraph A) (c : H.ConnectedComponent) :
    DecidablePred (fun a => a ∈ c.supp) := fun _ => Classical.propDecidable _

variable {V : Type*} [Fintype V]

theorem central_boundary_fiber_card_one_of_not_bad (G : SimpleGraph V) (o : V)
    (ell r R : ℕ) (hmargin : ell + r + 1 ≤ R)
    (c : (centralBoundaryGraph G (graphBallVertices G o ell) r).ConnectedComponent)
    (a : BoundaryOrientedEdge G (graphBallVertices G o ell))
    (ha : centralBoundaryCenter G (graphBallVertices G o ell) r a ∈ c.supp)
    (hnot : a ∉ multiattachmentBoundaryLabels G o (by omega : ell + 1 ≤ R)) :
    Nat.card (CentralBoundaryFiber G (graphBallVertices G o ell) r c) = 1 := by
  have hle := central_boundary_fiber_card_le_ambient G o ell r R hmargin c a ha
  rw [ambientBoundaryFiber_card_one_of_not_bad G o (by omega) a hnot] at hle
  have hnonempty : Nonempty (CentralBoundaryFiber G (graphBallVertices G o ell) r c) := ⟨⟨a, ha⟩⟩
  have hfinite : Finite (CentralBoundaryFiber G (graphBallVertices G o ell) r c) :=
    Finite.of_injective (fun e : CentralBoundaryFiber G (graphBallVertices G o ell) r c => e.val) Subtype.val_injective
  have hpos := Nat.card_pos_iff.mpr ⟨hnonempty, hfinite⟩
  omega

/-- No second original boundary label belongs to this good central component. -/
theorem central_boundary_label_eq_of_not_bad (G : SimpleGraph V) (o : V)
    (ell r R : ℕ) (hmargin : ell + r + 1 ≤ R)
    (c : (centralBoundaryGraph G (graphBallVertices G o ell) r).ConnectedComponent)
    (a b : BoundaryOrientedEdge G (graphBallVertices G o ell))
    (ha : centralBoundaryCenter G (graphBallVertices G o ell) r a ∈ c.supp)
    (hb : centralBoundaryCenter G (graphBallVertices G o ell) r b ∈ c.supp)
    (hnot : a ∉ multiattachmentBoundaryLabels G o (by omega : ell + 1 ≤ R)) : b = a := by
  have hcard := central_boundary_fiber_card_one_of_not_bad G o ell r R hmargin c a ha hnot
  have hsub := (Nat.card_eq_one_iff_unique.mp hcard).1
  exact congrArg Subtype.val (hsub.elim (⟨b, hb⟩ : CentralBoundaryFiber G (graphBallVertices G o ell) r c) ⟨a, ha⟩)

namespace RegularGraph
variable {N d : ℕ}

theorem central_component_deficit_sum_one_of_not_bad (g : RegularGraph N d) (o : Fin N)
    (ell r R : ℕ) (hmargin : ell + r + 1 ≤ R)
    (c : (centralBoundaryGraph g.graph (graphBallVertices g.graph o ell) r).ConnectedComponent)
    (a : BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
    (ha : centralBoundaryCenter g.graph (graphBallVertices g.graph o ell) r a ∈ c.supp)
    (hnot : a ∉ multiattachmentBoundaryLabels g.graph o (by omega : ell + 1 ≤ R)) :
    (∑ v : c.supp, (((g.deficient.delete (graphBallVertices g.graph o ell)).restrict
      (centralBoundaryVertices g.graph (graphBallVertices g.graph o ell) r)).restrict c.supp).deficit v) = 1 := by
  have hh := g.central_component_deficit_sum_eq_labels (graphBallVertices g.graph o ell) r c
  simp only [← finsum_eq_sum_of_fintype] at hh ⊢
  exact hh.trans (central_boundary_fiber_card_one_of_not_bad g.graph o ell r R hmargin c a ha hnot)

end RegularGraph
end LocalLaw
