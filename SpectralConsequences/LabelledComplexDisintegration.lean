import SpectralConsequences.FiniteExpectationMarginal
import SpectralConsequences.ProductCoordinateMeans
import LocalLaw.BallResamplingMeasure

/-! Exact arbitrary-complex conditional expectation for the actual labelled
regular-graph sampling space. No event-marginal assumption is introduced. -/
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1800000
namespace SpectralConsequences
open LocalLaw
local instance labelledComplexDisintegrationDecidable (p:Prop):Decidable p:=Classical.propDecidable p

def graphLabelledFiber (N d:ℕ)(T:Set (Fin N))(g:RegularGraph N d):Type:=
  LabelledBoundaryFiber ((regularBoundaryDecomposition N d T).symm g).2

instance graphLabelledFiberFintype (N d:ℕ)(T:Set (Fin N))(g:RegularGraph N d):
    Fintype (graphLabelledFiber N d T g):=by
  unfold graphLabelledFiber
  infer_instance

def globalGraphFiberEquiv (N d:ℕ)(T:Set (Fin N)):
    GlobalLabelledSpace N d T≃Σg:RegularGraph N d,graphLabelledFiber N d T g:=
  (Equiv.sigmaAssoc (fun (μ:Fin (N*d+1)) (g:RegularBoundaryBlock N d μ.val T)=>
    LabelledBoundaryFiber g)).symm.trans
      (Equiv.sigmaCongrLeft' (regularBoundaryDecomposition N d T))

def canonicalGlobalLabelledState (N d:ℕ)(T:Set (Fin N))(g:RegularGraph N d)
    (data:graphLabelledFiber N d T g):GlobalLabelledSpace N d T:=
  (globalGraphFiberEquiv N d T).symm ⟨g,data⟩

theorem canonicalGlobalLabelledState_project (N d:ℕ)(T:Set (Fin N))(g:RegularGraph N d)
    (data:graphLabelledFiber N d T g):
    globalLabelledProject (canonicalGlobalLabelledState N d T g data)=g:=by rfl

def globalLabelledConditionalMean (N d:ℕ)(T:Set (Fin N))
    (f:GlobalLabelledSpace N d T→ℂ)(g:RegularGraph N d):ℂ:=
  finiteComplexMean (fun data:graphLabelledFiber N d T g=>
    f (canonicalGlobalLabelledState N d T g data))

theorem global_labelled_complex_disintegration (N d:ℕ)(T:Set (Fin N))
    (f:GlobalLabelledSpace N d T→ℂ):
    finiteExpectation (globalLabelledWeight N d T) f=
      finiteExpectation (RegularGraph.weight (N:=N) (d:=d))
        (globalLabelledConditionalMean N d T f):=by
  have hsum:finiteExpectation (globalLabelledWeight N d T) f=
      finiteExpectation
        (finiteFiberWeight (graphLabelledFiber N d T) (RegularGraph.weight (N:=N) (d:=d)))
        (fun s=>f (canonicalGlobalLabelledState N d T s.1 s.2)):=by
    unfold finiteExpectation
    symm
    apply Fintype.sum_equiv (globalGraphFiberEquiv N d T).symm
    intro s
    rfl
  rw [hsum,finiteExpectation_fiber]
  rfl

theorem globalLabelledConditionalMean_prod (N d:ℕ)(T:Set (Fin N))
    (f:GlobalLabelledSpace N d T→ℂ)(g:RegularGraph N d):
    globalLabelledConditionalMean N d T f g=
      finiteComplexMean (fun labels:Fin (Nat.card (BoundaryOrientedEdge g.graph T))≃
        BoundaryOrientedEdge g.graph T=>
          finiteComplexMean (fun samples:LocalSamplingFiber g.graph T=>
            f (canonicalGlobalLabelledState N d T g (labels,samples)))):=by
  exact finiteComplexMean_prod _

end SpectralConsequences
