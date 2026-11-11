import LocalLaw.OldTwoTargetAugmentation
import LocalLaw.ComponentRestrictionBudget

/-!
# Every switched pair ball lies in the old endpoint-and-two-target union

The union of balls around all surgery endpoints and the two fixed targets
is literally invariant. Thus even a switched pair whose finite reference
class is not known is an inherited restriction of an OLD augmented model.
-/
noncomputable section
namespace LocalLaw
local instance augmentedPairCaptureDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace LabelledResamplingState
variable {V : Type} {T : Set V} {ι : Type} [Fintype ι]

omit [Fintype ι] in
theorem twoTargetEndpointVertices_eq_setBall (s : LabelledResamplingState V T ι)
    (selector r : ℕ) (x y : (Tᶜ : Set V)) :
    s.twoTargetEndpointVertices selector r x y=
      graphSetBall (outsideGraph s.graph T) (s.endpointModelRoots selector∪{x,y}) r := by
  ext v
  constructor
  · rintro (⟨a,ha,hd⟩ | (hx | hy))
    · exact ⟨a,Or.inl ha,hd⟩
    · exact ⟨x,Or.inr (Or.inl rfl),hx⟩
    · exact ⟨y,Or.inr (Or.inr rfl),hy⟩
  · rintro ⟨a,ha,hd⟩
    rcases ha with ha | (ha | ha)
    · exact Or.inl ⟨a,ha,hd⟩
    · exact Or.inr (Or.inl (ha ▸ hd))
    · exact Or.inr (Or.inr (ha ▸ hd))

theorem twoTargetEndpointVertices_new_setBall (s : LabelledResamplingState V T ι)
    (selector r : ℕ) (x y : (Tᶜ : Set V)) :
    s.twoTargetEndpointVertices selector r x y=
      graphSetBall (outsideGraph (s.fullResample selector).graph T) (s.endpointModelRoots selector∪{x,y}) r := by
  rw [s.twoTargetEndpointVertices_eq_setBall selector r x y]
  apply graphSetBall_eq_of_internal_changes
  intro u v huv
  have capture:=s.fullResampleOutsideEndpoints_subset_modelRoots selector
  rcases huv with hu | hv
  · exact (s.fullResample_outside_adj_of_away_left selector u v
      (fun hh=>hu (Or.inl (capture hh)))).symm
  · rw [(outsideGraph s.graph T).adj_comm,(outsideGraph (s.fullResample selector).graph T).adj_comm]
    exact (s.fullResample_outside_adj_of_away_left selector v u
      (fun hh=>hv (Or.inl (capture hh)))).symm

theorem switched_pairBall_subset_old_augmentation (s : LabelledResamplingState V T ι)
    (selector r : ℕ) (x y : (Tᶜ : Set V)) :
    pairBallVertices (outsideGraph (s.fullResample selector).graph T) x y r⊆
      s.twoTargetEndpointVertices selector r x y := by
  intro v hv
  rw [s.twoTargetEndpointVertices_new_setBall selector r x y]
  rcases hv with hx | hy
  · exact ⟨x,Or.inr (Or.inl rfl),hx⟩
  · exact ⟨y,Or.inr (Or.inr rfl),hy⟩

end LabelledResamplingState

namespace DeficientGraph
variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

omit [DecidableEq V] in
/-- A literal subset inherits the componentwise budget of the larger
restriction, with deficits transported unchanged. -/
theorem subset_restriction_component_budget (g : DeficientGraph V d) (S K : Set V)
    (hKS : K⊆S) (hbudget : (g.restrict S).ComponentFiniteReferenceBudget) :
    (g.restrict K).ComponentFiniteReferenceBudget := by
  let U:Set S:={v | v.val∈K}
  let e : (g.restrict K).graph≃g((g.restrict S).restrict U).graph :=
    { toEquiv :=
        { toFun:=fun v=>⟨⟨v.val,hKS v.property⟩,v.property⟩
          invFun:=fun v=>⟨v.val.val,v.property⟩
          left_inv:=fun _=>rfl
          right_inv:=fun _=>rfl }
      map_rel_iff':=Iff.rfl }
  have hh:=(g.restrict S).restrict_componentFiniteReferenceBudget U hbudget
  exact ((g.restrict S).restrict U).componentFiniteReferenceBudget_of_iso (g.restrict K) e
    (fun _=>rfl) hh

end DeficientGraph

namespace RegularGraph
variable {N d : ℕ} {ι : Type} [Fintype ι]

theorem switched_pair_old_model_component_budget (g : RegularGraph N d) (o : Fin N)
    (ell selector r R : ℕ) (hmargin : 7*r+6*ell+8≤R) (hsep : 2*r+2≤selector)
    (hballs : ∀ v,graphBallExcess g.graph v R≤finiteOmega d)
    (labels : ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
    (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o ell))
    (x y : ((graphBallVertices g.graph o ell)ᶜ : Set (Fin N))) :
    let T:=graphBallVertices g.graph o ell
    let s:=g.admissibleState T labels samples
    ((g.deficient.delete T).restrict
      (pairBallVertices (outsideGraph (s.fullResample selector).graph T) x y r)).ComponentFiniteReferenceBudget := by
  let T:=graphBallVertices g.graph o ell
  let s:=g.admissibleState T labels samples
  exact (g.deficient.delete T).subset_restriction_component_budget
    (s.twoTargetEndpointVertices selector r x y)
    (pairBallVertices (outsideGraph (s.fullResample selector).graph T) x y r)
    (s.switched_pairBall_subset_old_augmentation selector r x y)
    (g.old_twoTargetEndpoint_component_budget o ell selector r R hmargin hsep hballs labels samples x y)

end RegularGraph
end LocalLaw
