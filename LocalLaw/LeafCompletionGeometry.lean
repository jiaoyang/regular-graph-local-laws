import LocalLaw.DeletedLeafReferenceBudget
import LocalLaw.MultiLeafRestriction
import LocalLaw.HereditaryReferenceBounds

/-! # Both literal common leaf models have proved class and diameter

The global model splits the actual removed vertices into lost-edge leaf
slots. The local model retains every slot whose mate lies in K. Reference
class, common metric, intrinsic diameter and pair-ball capture are all
conclusions from the old finite model; no comparison estimate is assumed.
-/

noncomputable section
set_option maxHeartbeats 2400000
namespace LocalLaw
local instance leafCompletionGeometryDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace DeficientGraph
variable {V:Type}[Fintype V]{d:ℕ}

theorem leaf_completion_global_local_geometry (g:DeficientGraph V d)(hd:1≤d)
    (T:Set V)(K:Set (Tᶜ:Set V))(hbudget:g.ComponentFiniteReferenceBudget)
    (D:ℕ)(hD:∀u v,g.graph.dist u v≤D) :
    let H:=g.deletedLeafModel hd T
    let U:=multiLeafLift (deletedLeafMate g.graph T) K
    H.ComponentFiniteReferenceBudget ∧ (H.restrict U).ComponentFiniteReferenceBudget ∧
    (∀u v,H.graph.dist u v≤hereditaryReferenceRadius d D+2) ∧
    (∀u v,(H.restrict U).graph.dist u v≤hereditaryReferenceRadius d D+2) := by
  dsimp only
  let H:=g.deletedLeafModel hd T
  let mate:=deletedLeafMate g.graph T
  let U:=multiLeafLift mate K
  let D1:=hereditaryReferenceRadius d D
  have hbase:=g.deletedLeafModel_component_finite_budget hd T hbudget
  have hlocal:=H.restrict_componentFiniteReferenceBudget U hbase
  have hcore:∀u v:(Tᶜ:Set V),(g.delete T).graph.dist u v≤D1:=by
    intro u v
    exact g.finite_class_restriction_intrinsic_diameter hbudget D hD Tᶜ u v
  have hcoreLocal:∀u v:K,((g.delete T).graph.induce K).dist u v≤D1:=by
    let f:K→V:=fun v=>v.val.val
    have hf:Function.Injective f:=fun _ _ h=>Subtype.ext (Subtype.ext h)
    let A:=Set.range f
    let e:((g.delete T).graph.induce K)≃g g.graph.induce A:=
      {toEquiv:=Equiv.ofInjective f hf,map_rel_iff':=Iff.rfl}
    intro u v
    have hh:=g.finite_class_restriction_intrinsic_diameter hbudget D hD A (e u) (e v)
    exact (graphIso_dist e u v).symm.le.trans hh
  refine ⟨hbase,hlocal,?_,?_⟩
  · exact multiLeafGraph_diameter_bound (g.delete T).graph mate D1 hcore
  · intro u v
    let e:=multiLeafLiftGraphIso (g.delete T).graph mate K
    have hh:=multiLeafGraph_diameter_bound ((g.delete T).graph.induce K)
      (multiLeafLiftMate mate K) D1 hcoreLocal (e.symm u) (e.symm v)
    have he:=graphIso_dist e (e.symm u) (e.symm v)
    simp only [e.apply_symm_apply] at he
    exact he.le.trans hh

theorem leaf_completion_pair_capture (g:DeficientGraph V d)(hd:1≤d)
    (T:Set V)(K:Set (Tᶜ:Set V))(x y:(Tᶜ:Set V))(r:ℕ)
    (hcapture:pairBallVertices (g.delete T).graph x y r⊆K) :
    pairBallVertices (g.deletedLeafModel hd T).graph (.inl x) (.inl y) r⊆
      multiLeafLift (deletedLeafMate g.graph T) K :=
  multiLeafLift_pair_capture (g.delete T).graph (deletedLeafMate g.graph T) K x y r hcapture

end DeficientGraph
end LocalLaw
