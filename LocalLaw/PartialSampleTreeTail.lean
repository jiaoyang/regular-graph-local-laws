import LocalLaw.RestrictedTreePatchTail
import LocalLaw.EndpointBranchDeficits

/-! # Actual eligible sample blocks in arbitrary old restrictions

Eligibility supplies the ambient tree patch and exact zero inherited deficit.
The arbitrary old restriction may cut that patch in any shape. Its genuine
physical-boundary entries still have the proved pure tree-tail error.
-/

noncomputable section
namespace LocalLaw
local instance partialSampleTreeTailDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ} {ι : Type}

theorem eligible_sample_root_tree_zero_ball (g : RegularGraph N d) (T : Set (Fin N))
    (labels : ι≃BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T)
    (selector R : ℕ) (hR : R+1≤selector)
    (i : (g.admissibleState T labels samples).AdmissibleSampleIndex selector)
    (c : (Tᶜ:Set (Fin N)))
    (hc : c∈(g.admissibleState T labels samples).admissiblePairRoots selector i) :
    (graphBall (outsideGraph g.graph T) c R).IsTree ∧
      ∀ v∈graphBallVertices (outsideGraph g.graph T) c R,(g.deficient.delete T).deficit v=0 := by
  let s := g.admissibleState T labels samples
  let H := outsideGraph g.graph T
  let P := s.sampledEndpointPatch selector R i
  have hsubset : graphBallVertices H c R⊆P := fun v hv => ⟨c,hc,hv⟩
  have htree := s.sampledEndpointPatch_isTree selector R (by omega) i
  let f : graphBall H c R →g H.induce P :=
    { toFun := fun v => ⟨v.val,hsubset v.property⟩
      map_rel' := fun h => h }
  have hf : Function.Injective f := by
    intro u v h
    exact Subtype.ext (congrArg (fun x : P => x.val) h)
  constructor
  · constructor
    · exact graphBall_connected H c R
    · intro v p hp
      exact htree.IsAcyclic (p.map f) (hp.map hf)
  · intro v hv
    exact g.sampledEndpointPatch_zero_deficit T labels samples selector R hR i v (hsubset hv)


theorem partial_sample_diagonal_physical_tail (g : RegularGraph N d) (hd : 3≤d)
    (T : Set (Fin N)) (labels : ι≃BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T)
    (selector r : ℕ) (hr : r+1≤selector)
    (i : (g.admissibleState T labels samples).AdmissibleSampleIndex selector)
    (S : Set (Tᶜ:Set (Fin N))) (hbudget : ((g.deficient.delete T).restrict S).ComponentFiniteReferenceBudget)
    (x : S) (hx : x.val∈(g.admissibleState T labels samples).admissiblePairRoots selector i)
    (z : ℂ) (hz : 0<z.im) :
    ‖((g.deficient.delete T).restrict S).extensionGreen (semicircleRoot z) z x x-graphKestenMcKayReference d z‖≤
      physicalModelTailConstant d*physicalTransfer d z^(2*r) := by
  have hp := g.eligible_sample_root_tree_zero_ball T labels samples selector r hr i x.val hx
  exact (g.deficient.delete T).restrict_tree_diagonal_physical_tail hd S hbudget x r hp.1 hp.2 z hz


theorem partial_sample_adjacent_physical_tail (g : RegularGraph N d) (hd : 3≤d)
    (T : Set (Fin N)) (labels : ι≃BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T)
    (selector r : ℕ) (hr : r+2≤selector)
    (i : (g.admissibleState T labels samples).AdmissibleSampleIndex selector)
    (S : Set (Tᶜ:Set (Fin N))) (hbudget : ((g.deficient.delete T).restrict S).ComponentFiniteReferenceBudget)
    (x y : S)
    (hx : x.val=(g.admissibleState T labels samples).admissibleSampleVertex selector i)
    (hy : y.val=(g.admissibleState T labels samples).admissibleSecondVertex selector i)
    (z : ℂ) (hz : 0<z.im) :
    ‖((g.deficient.delete T).restrict S).extensionGreen (semicircleRoot z) z x y-
      graphKestenMcKayReference d z*(-semicircleRoot z*treeEdgeWeight d)‖≤
      physicalModelTailConstant d*physicalTransfer d z^(2*r) := by
  let s := g.admissibleState T labels samples
  have hxpair : x.val∈s.admissiblePairRoots selector i := by
    rw [hx]
    simp only [LabelledResamplingState.admissiblePairRoots,Set.mem_insert_iff,Set.mem_singleton_iff]
    exact Or.inl rfl
  have hp := g.eligible_sample_root_tree_zero_ball T labels samples selector (r+1) (by omega) i x.val hxpair
  have hxy : (outsideGraph g.graph T).Adj x.val y.val := by
    rw [hx,hy]
    exact (samples (labels i.val)).property.1
  exact (g.deficient.delete T).restrict_tree_adjacent_physical_tail hd S hbudget x y hxy r hp.1 hp.2 z hz

end RegularGraph
end LocalLaw
