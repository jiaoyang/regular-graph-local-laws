import LocalLaw.FullEndpointBranches
import LocalLaw.PendantForestExcess
import LocalLaw.ComponentFiniteLocalization

/-! # Actual base reference class for the complete filled switched model

The new core may be disconnected. Its edges form a subgraph of the old
expanded root ball. Every exterior piece is an actual tree with one cut,
so finite even-pattern transfer proves the component excess budget.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2200000
namespace LocalLaw
local instance fullEndpointBudgetDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance (priority := high) fullEndpointBudgetComponentDecidable {A : Type*}
    (G : SimpleGraph A) (C : G.ConnectedComponent) : DecidablePred (fun x => x∈C.supp) :=
  fun _ => Classical.propDecidable _
namespace LabelledResamplingState
variable {V : Type} [Fintype V] {T : Set V} {ι : Type} [Fintype ι]

theorem fullEndpoint_component_excess (s : LabelledResamplingState V T ι)
    (selector r ω : ℕ) (hsep : 2*r+2≤selector)
    (hcore : graphExcess (s.graph.induce (filledExteriorVertices T (s.centralEndpointPatch r)))≤ω)
    (C : ((s.fullResample selector).graph.induce
      (filledExteriorVertices T (s.endpointModelVertices selector r))).ConnectedComponent) :
    graphExcess (((s.fullResample selector).graph.induce
      (filledExteriorVertices T (s.endpointModelVertices selector r))).induce C.supp)≤ω := by
  let K := filledExteriorVertices T (s.endpointModelVertices selector r)
  let L := filledExteriorVertices T (s.centralEndpointPatch r)
  let G := (s.fullResample selector).graph.induce K
  let H := s.graph.induce K
  let S := s.fullEndpointCore selector r
  have hLK : L⊆K := by
    rintro x (hx | ⟨v,hv,rfl⟩)
    · exact Or.inl hx
    · exact Or.inr ⟨v,s.centralEndpointPatch_subset_model selector r hv,rfl⟩
  have hcut := s.fullEndpoint_tree_cut_components selector r hsep
  have hbound := pendant_forest_connected_embedding_excess_le (G.induce C.supp) G H S
    (Function.Embedding.subtype C.supp) C.connected_induce_supp (fun h => h)
    (fun c => (hcut.1 c).IsAcyclic) (fun c => (hcut.2 c).le)
    (fun {u v} hu hv huv => s.fullEndpoint_core_edges_old selector r hsep u v hu hv huv)
  let e := inducePreimageIso s.graph K L hLK
  have heq : graphExcess (H.induce S)=graphExcess (s.graph.induce L) := graphExcess_iso e
  exact hbound.trans (heq.le.trans hcore)

end LabelledResamplingState
namespace RegularGraph
variable {N d : ℕ} {ι : Type} [Fintype ι]

theorem filledEndpoint_component_reference_budget (g : RegularGraph N d)
    (o : Fin N) (ell selector r R : ℕ)
    (boundary : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
    (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o ell))
    (hsep : 2*r+2≤selector) (hmargin : ell+r+1≤R)
    (hex : graphBallExcess g.graph o R≤finiteOmega d) :
    let T := graphBallVertices g.graph o ell
    let s := g.admissibleState T boundary samples
    ((g.labelledResampledGraph T boundary samples selector).filledExteriorModel T
      (s.endpointModelVertices selector r)).ComponentReferenceBudget := by
  let T := graphBallVertices g.graph o ell
  let s := g.admissibleState T boundary samples
  let gnew := g.labelledResampledGraph T boundary samples selector
  let M := gnew.filledExteriorModel T (s.endpointModelVertices selector r)
  have hcore : graphExcess (s.graph.induce (filledExteriorVertices T (s.centralEndpointPatch r)))≤finiteOmega d := by
    change graphExcess (g.graph.induce (filledExteriorVertices T (centralBoundaryVertices g.graph T r)))≤_
    rw [filled_centralBoundary_eq_ball]
    exact (graphBallExcess_mono_radius g.graph o hmargin).trans hex
  change M.ComponentReferenceBudget
  intro C
  have hh := s.fullEndpoint_component_excess selector r (finiteOmega d) hsep hcore C
  have hzero : (∑ v, (M.restrict C.supp).deficit v)=0 := by
    apply Finset.sum_eq_zero
    intro v _
    rfl
  rw [hzero,Nat.zero_add]
  exact hh

end RegularGraph
end LocalLaw
