import LocalLaw.DetachedEndpointModel
import LocalLaw.OldEndpointComponentCounts

/-! # Exact diagonal rows at detached c-roots in the endpoint matrix -/

noncomputable section
namespace LocalLaw
local instance detachedEndpointRowsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace LabelledResamplingState
variable {V : Type} [Fintype V] {T : Set V} {ι : Type*} [Fintype ι]

def endpointTipRoot (s : LabelledResamplingState V T ι) (selector : ℕ)
    (i : s.AdmissibleSampleIndex selector) : s.endpointModelRoots selector :=
  ⟨s.admissibleSecondVertex selector i, Or.inr (Set.mem_iUnion.mpr ⟨i, Or.inr rfl⟩)⟩

omit [Fintype V] [Fintype ι] in
theorem endpointRoot_mem_secondBranch_iff (s : LabelledResamplingState V T ι) (selector r : ℕ)
    (hsep : 2 * r + 2 ≤ selector) (i : s.AdmissibleSampleIndex selector)
    (v : s.endpointModelRoots selector) :
    v.val ∈ s.sampledSecondBranch selector r i ↔ v.val = s.admissibleSecondVertex selector i := by
  constructor
  · intro hv
    have hp := s.endpointRoot_in_sampled_is_pair selector r hsep i v
      (s.sampledSecondBranch_subset selector r i hv)
    rcases hp with hb | hc
    · have hB : v.val ∈ s.sampledFirstBranch selector r i :=
        hb ▸ s.admissibleSampleVertex_mem_firstBranch selector r i
      exact False.elim (Set.disjoint_left.mp (s.sampledBranch_disjoint selector r (by omega) i) hB hv)
    · exact hc
  · intro h
    exact h ▸ s.admissibleSecondVertex_mem_secondBranch selector r i

end LabelledResamplingState

namespace RegularGraph
variable {N d : ℕ} {ι : Type*} [Fintype ι]

theorem switchedEndpointModel_tip_endpoint_row (g : RegularGraph N d) (hd : 3 ≤ d)
    (T : Set (Fin N)) (boundary : ι ≃ BoundaryOrientedEdge g.graph T) (S : LocalSamplingFiber g.graph T)
    (selector r : ℕ) (hsep : 2 * r + 2 ≤ selector) (hr : r + 2 ≤ selector)
    (i : (g.admissibleState T boundary S).AdmissibleSampleIndex selector)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (v : (g.admissibleState T boundary S).endpointModelRoots selector) :
    let s := g.admissibleState T boundary S
    let e := s.endpointModelKernelEmbedding selector r
    (g.switchedEndpointModel T boundary S selector r).extensionGreen q z
      (e (s.endpointTipRoot selector i)) (e v) =
        if v = s.endpointTipRoot selector i then cavityIterate z q (r + 1) else 0 := by
  dsimp only
  let s := g.admissibleState T boundary S
  by_cases hv : v = s.endpointTipRoot selector i
  · rw [if_pos hv, hv]
    exact g.switchedEndpointModel_tip_diagonal hd T boundary S selector r hsep hr i q z hz hq
  · rw [if_neg hv]
    have hnot : v.val ∉ s.sampledSecondBranch selector r i := fun h =>
      hv (Subtype.ext ((s.endpointRoot_mem_secondBranch_iff selector r hsep i v).mp h))
    exact g.switchedEndpointModel_tip_zero_across_branch hd T boundary S selector r hsep i q z hz hq
      (s.endpointModelKernelEmbedding selector r v) hnot

end RegularGraph
end LocalLaw
