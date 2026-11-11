import LocalLaw.OldEndpointComponentCounts
import LocalLaw.SourceEndpointCorrelations

/-! # Actual old common-model zero rows outside a sampled pair -/

noncomputable section
namespace LocalLaw
local instance endpointOldModelRowsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ} {ι : Type} [Fintype ι]

omit [Fintype ι] in
theorem endpointModel_pair_zero_outside (g : RegularGraph N d) (hd : 3≤d) (T : Set (Fin N))
    (labels : ι ≃ BoundaryOrientedEdge g.graph T) (S : LocalSamplingFiber g.graph T)
    (selector r : ℕ) (hsep : 2*r+2≤selector)
    (i : (g.admissibleState T labels S).AdmissibleSampleIndex selector)
    (q z : ℂ) (hz : 0<z.im) (hq : 0≤q.im) :
    let s := g.admissibleState T labels S
    ∀ u ∈ s.endpointPairFinset selector i, ∀ v ∉ s.endpointPairFinset selector i,
      (g.endpointModel T labels S selector r).extensionGreen q z
        (s.endpointRootVertex selector r u) (s.endpointRootVertex selector r v)=0 := by
  dsimp only
  let s := g.admissibleState T labels S
  let M := g.endpointModel T labels S selector r
  let patch : Set (s.endpointModelVertices selector r) := {x | x.val ∈ s.sampledEndpointPatch selector r i}
  have hcut : ∀ x ∈ patch, ∀ y ∉ patch, ¬M.graph.Adj x y := by
    intro x hx y hy hxy
    exact s.endpointModel_sampled_closed selector r hsep i x.val x.property hx y.val y.property hy hxy
  intro u hu v hv
  have hupair := (s.mem_endpointPairFinset_iff selector i u).mp hu
  have huPatch : s.endpointRootVertex selector r u ∈ patch := ⟨u.val,hupair,by
    change (outsideGraph s.graph T).edist u.val u.val ≤ (r : ℕ∞)
    simp⟩
  have hvPatch : s.endpointRootVertex selector r v ∉ patch := by
    intro h
    exact hv ((s.mem_endpointPairFinset_iff selector i v).mpr
      (s.endpointRoot_in_sampled_is_pair selector r hsep i v h))
  exact M.extensionGreen_zero_across_cut hd patch hcut q z hz hq _ huPatch _ hvPatch

end RegularGraph
end LocalLaw
