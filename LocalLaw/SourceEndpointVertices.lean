import LocalLaw.SourceEndpointMatrices

/-! # Named actual indices in the deduplicated endpoint matrices -/

noncomputable section
namespace LocalLaw
local instance sourceEndpointVerticesDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ} {ι : Type} [Fintype ι]

def sourceEndpointBoundaryIndex (g : RegularGraph N d) (T : Set (Fin N))
    (boundary : ι ≃ BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T)
    (selector : ℕ) (α : BoundaryOrientedEdge g.graph T) :
    (g.admissibleState T boundary samples).endpointModelRoots selector :=
  ⟨boundaryOutsideVertex g.graph T α, Or.inl ⟨α, rfl⟩⟩

def sourceEndpointBaseIndex (g : RegularGraph N d) (T : Set (Fin N))
    (boundary : ι ≃ BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T)
    (selector : ℕ) (i : (g.admissibleState T boundary samples).AdmissibleSampleIndex selector) :
    (g.admissibleState T boundary samples).endpointModelRoots selector :=
  ⟨(g.admissibleState T boundary samples).admissibleSampleVertex selector i,
    Or.inr (Set.mem_iUnion.mpr ⟨i, Or.inl rfl⟩)⟩

def sourceEndpointTipIndex (g : RegularGraph N d) (T : Set (Fin N))
    (boundary : ι ≃ BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T)
    (selector : ℕ) (i : (g.admissibleState T boundary samples).AdmissibleSampleIndex selector) :
    (g.admissibleState T boundary samples).endpointModelRoots selector :=
  ⟨(g.admissibleState T boundary samples).admissibleSecondVertex selector i,
    Or.inr (Set.mem_iUnion.mpr ⟨i, Or.inr rfl⟩)⟩

omit [Fintype ι] in
theorem sourceEndpointBaseIndex_kernelEmbedding (g : RegularGraph N d) (T : Set (Fin N))
    (boundary : ι ≃ BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T)
    (selector r : ℕ) (i : (g.admissibleState T boundary samples).AdmissibleSampleIndex selector) :
    (g.admissibleState T boundary samples).endpointModelKernelEmbedding selector r
      (g.sourceEndpointBaseIndex T boundary samples selector i) =
        (g.admissibleState T boundary samples).endpointBaseVertex selector r i := rfl

omit [Fintype ι] in
theorem sourceEndpointTipIndex_kernelEmbedding (g : RegularGraph N d) (T : Set (Fin N))
    (boundary : ι ≃ BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T)
    (selector r : ℕ) (i : (g.admissibleState T boundary samples).AdmissibleSampleIndex selector) :
    (g.admissibleState T boundary samples).endpointModelKernelEmbedding selector r
      (g.sourceEndpointTipIndex T boundary samples selector i) =
        (g.admissibleState T boundary samples).endpointTipVertex selector r i := rfl

theorem sourceEndpointQ_tip_diagonal (g : RegularGraph N d) (hd : 3 ≤ d) (T : Set (Fin N))
    (boundary : ι ≃ BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T)
    (selector r : ℕ) (hsep : 2 * r + 2 ≤ selector) (hr : r + 2 ≤ selector)
    (i : (g.admissibleState T boundary samples).AdmissibleSampleIndex selector)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    let c := g.sourceEndpointTipIndex T boundary samples selector i
    g.sourceEndpointQ T boundary samples selector r q z c c = cavityIterate z q (r + 1) :=
  g.switchedEndpointModel_tip_diagonal hd T boundary samples selector r hsep hr i q z hz hq

theorem sourceEndpointQ_tip_base_zero (g : RegularGraph N d) (hd : 3 ≤ d) (T : Set (Fin N))
    (boundary : ι ≃ BoundaryOrientedEdge g.graph T) (samples : LocalSamplingFiber g.graph T)
    (selector r : ℕ) (hsep : 2 * r + 2 ≤ selector)
    (i : (g.admissibleState T boundary samples).AdmissibleSampleIndex selector)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    g.sourceEndpointQ T boundary samples selector r q z
      (g.sourceEndpointTipIndex T boundary samples selector i)
      (g.sourceEndpointBaseIndex T boundary samples selector i) = 0 := by
  let s := g.admissibleState T boundary samples
  let D := s.endpointBranchAttachmentData selector r hsep
  have hnot : (s.endpointBaseVertex selector r i).val ∉ s.sampledSecondBranch selector r i := by
    intro h
    exact Set.disjoint_left.mp (D.branch_disjoint i) (D.base_mem i) h
  exact g.switchedEndpointModel_tip_zero_across_branch hd T boundary samples selector r hsep i q z hz hq
    (s.endpointBaseVertex selector r i) hnot

end RegularGraph
end LocalLaw
