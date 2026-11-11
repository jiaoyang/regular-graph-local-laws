import LocalLaw.BranchRestorationBudget
import LocalLaw.EndpointRestorationInputs

/-! # Actual switched endpoint models belong to the finite reference class

The old ball excess bound, I/J-selected tree patches, and literal inherited
deficit conservation discharge every hypothesis of the restoration proof.
Every selected b-root lies in a base-class post component.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 3000000
namespace LocalLaw
local instance switchedEndpointBudgetDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance (priority := high) switchedEndpointBudgetComponentMem {A : Type*}
    (G : SimpleGraph A) (c : G.ConnectedComponent) : DecidablePred (fun a => a ∈ c.supp) :=
  fun _ => Classical.propDecidable _
namespace RegularGraph
variable {N d : ℕ} {ι : Type*} [Fintype ι]

theorem switchedEndpointModel_component_budget (g : RegularGraph N d) (hd : 3 ≤ d) (o : Fin N)
    (ell selector r R : ℕ) (hcentral : ell + r + 1 ≤ R) (hsep : 2 * r + 2 ≤ selector)
    (hbudget : graphBallExcess g.graph o R ≤ finiteOmega d)
    (boundary : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
    (S : LocalSamplingFiber g.graph (graphBallVertices g.graph o ell)) :
    (g.switchedEndpointModel (graphBallVertices g.graph o ell) boundary S selector r).ComponentFiniteReferenceBudget := by
  let T := graphBallVertices g.graph o ell
  let s := g.admissibleState T boundary S
  let old := g.endpointModel T boundary S selector r
  let post := g.switchedEndpointModel T boundary S selector r
  let D := s.endpointBranchAttachmentData selector r hsep
  have hcore : post.graph.induce D.core = old.graph.induce D.core :=
    s.endpoint_core_graph_eq selector r hsep
  have hB : ∀ i, (post.graph.induce (D.B i)).IsTree := s.endpoint_B_isTree selector r hsep
  have hC : ∀ i, (post.graph.induce (D.C i)).IsTree := s.endpoint_C_isTree selector r hsep
  have hold : old.ComponentFiniteReferenceBudget :=
    g.endpointModel_component_budget o ell selector r R hcentral hsep hbudget boundary S
  exact D.componentFiniteReferenceBudget_of_restoration old post hcore hB hC hold
    (fun v => s.restoredBoundaryLabels selector v.val)
    (fun v hv => g.endpoint_core_deficit_restoration T boundary S selector r hsep v hv)
    (fun i v hv => g.endpoint_B_deficit_zero T boundary S selector r hsep i v hv)
    (fun i v hv => g.endpoint_C_deficit_one_root T boundary S selector r hsep i v hv)
    (finiteOmega_positive d hd)

theorem switchedEndpointModel_base_component_budget (g : RegularGraph N d) (o : Fin N)
    (ell selector r R : ℕ) (hcentral : ell + r + 1 ≤ R) (hsep : 2 * r + 2 ≤ selector)
    (hbudget : graphBallExcess g.graph o R ≤ finiteOmega d)
    (boundary : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
    (S : LocalSamplingFiber g.graph (graphBallVertices g.graph o ell))
    (i : (g.admissibleState (graphBallVertices g.graph o ell) boundary S).AdmissibleSampleIndex selector) :
    let s := g.admissibleState (graphBallVertices g.graph o ell) boundary S
    let M := g.switchedEndpointModel (graphBallVertices g.graph o ell) boundary S selector r
    let c := M.graph.connectedComponentMk (s.endpointBaseVertex selector r i)
    (∑ v, (M.restrict c.supp).deficit v) + graphExcess (M.restrict c.supp).graph ≤ finiteOmega d := by
  dsimp only
  let T := graphBallVertices g.graph o ell
  let s := g.admissibleState T boundary S
  let old := g.endpointModel T boundary S selector r
  let post := g.switchedEndpointModel T boundary S selector r
  let D := s.endpointBranchAttachmentData selector r hsep
  have hcore : post.graph.induce D.core = old.graph.induce D.core :=
    s.endpoint_core_graph_eq selector r hsep
  have hB : ∀ i, (post.graph.induce (D.B i)).IsTree := s.endpoint_B_isTree selector r hsep
  have hC : ∀ i, (post.graph.induce (D.C i)).IsTree := s.endpoint_C_isTree selector r hsep
  have hold : old.ComponentFiniteReferenceBudget :=
    g.endpointModel_component_budget o ell selector r R hcentral hsep hbudget boundary S
  exact D.base_component_reference_budget old post hcore hB hC hold
    (fun v => s.restoredBoundaryLabels selector v.val)
    (fun v hv => g.endpoint_core_deficit_restoration T boundary S selector r hsep v hv)
    (fun i v hv => g.endpoint_B_deficit_zero T boundary S selector r hsep i v hv)
    i (g.endpoint_attach_restored_positive T boundary S selector r i)

end RegularGraph
end LocalLaw
