import LocalLaw.FullEndpointPerturbation
import LocalLaw.EndpointSurgeryParameters
import LocalLaw.CavityDeletionParameters

/-! # The complete modified block has only polylogarithmically many indices -/

noncomputable section
namespace LocalLaw
local instance fullEndpointCardinalityDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace LabelledResamplingState
variable {V : Type} [Fintype V] {T : Set V} {ι : Type} [Fintype ι]

theorem fullEndpointRoots_card (s : LabelledResamplingState V T ι) (selector : ℕ) :
    Nat.card (s.fullEndpointRoots selector) ≤
      Nat.card T + 3 * Nat.card (BoundaryOrientedEdge s.graph T) := by
  let f : T ⊕ s.endpointModelRoots selector → s.fullEndpointRoots selector
    | Sum.inl x => ⟨x.val, Or.inl x.property⟩
    | Sum.inr x => ⟨x.val.val, Or.inr ⟨x.val, x.property, rfl⟩⟩
  have hf : Function.Surjective f := by
    rintro ⟨x, hx | ⟨y, hy, heq⟩⟩
    · exact ⟨Sum.inl ⟨x, hx⟩, rfl⟩
    · exact ⟨Sum.inr ⟨y, hy⟩, Subtype.ext heq⟩
  have hh := Nat.card_le_card_of_surjective f hf
  rw [Nat.card_sum] at hh
  exact hh.trans (Nat.add_le_add_left (s.endpointModelRoots_card selector) _)

end LabelledResamplingState

def fullEndpointCountConstant (d : ℕ) : ℝ := ((d : ℝ) + 1) * (1 + 3 * d)

namespace RegularGraph
variable {N d : ℕ} {ι : Type} [Fintype ι]

theorem fullEndpointRoots_card_log_bound (g : RegularGraph N d) (o : Fin N)
    (a ell selector : ℕ) (hd : 3 ≤ d) (hL : 1 ≤ Real.log (N : ℝ))
    (hell : ell ≤ doubleLogRadius a d N)
    (boundary : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
    (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o ell)) :
    (Nat.card ((g.admissibleState _ boundary samples).fullEndpointRoots selector) : ℝ) ≤
      fullEndpointCountConstant d * Real.log (N : ℝ) ^ (2 * a) := by
  have hn := (g.admissibleState _ boundary samples).fullEndpointRoots_card selector
  have hreal : (Nat.card ((g.admissibleState _ boundary samples).fullEndpointRoots selector) : ℝ) ≤
      (Nat.card (graphBallVertices g.graph o ell) : ℝ) +
        3 * (Nat.card (BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell)) : ℝ) := by
    exact_mod_cast hn
  have ht := g.ball_card_log_bound o a ell hd hL hell
  have hb := g.boundary_card_log_bound o a ell hd hL hell
  unfold fullEndpointCountConstant
  nlinarith only [hreal, ht, hb]

end RegularGraph
end LocalLaw
