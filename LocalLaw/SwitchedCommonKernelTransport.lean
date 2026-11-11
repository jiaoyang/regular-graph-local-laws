import LocalLaw.SourceCommonLeafKernelDecay
import LocalLaw.RestrictedCommonModel

/-! # The actual switched common-deleted kernel inherits the proved old bound -/

noncomputable section
namespace LocalLaw
local instance switchedCommonKernelDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace RegularGraph
variable {N d:ℕ}{ι:Type}[Fintype ι]

theorem switched_common_core_decay (g:RegularGraph N d)(T:Set (Fin N))
    (labels:ι≃BoundaryOrientedEdge g.graph T)(samples:LocalSamplingFiber g.graph T)
    (selector:ℕ)(A:Set (Tᶜ:Set (Fin N)))
    (hA:(g.admissibleState T labels samples).selectedFirstSet selector⊆A)
    (q z:ℂ)(K L ε:ℝ) :
    let B:=(g.admissibleState T labels samples).partialFirstRemovedSet selector A
    ((g.deficient.delete T).restrict A).LeafCoreDecayBound B q z K L ε→
      (((g.labelledResampledGraph T labels samples selector).deficient.delete T).restrict A).LeafCoreDecayBound B q z K L ε := by
  dsimp only
  intro hold
  unfold DeficientGraph.LeafCoreDecayBound at hold ⊢
  rw [g.restricted_selectedFirst_deletion_eq T labels samples selector A hA]
  exact hold

end RegularGraph
end LocalLaw
