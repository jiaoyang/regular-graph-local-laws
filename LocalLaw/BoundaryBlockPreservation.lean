import LocalLaw.EligibleBoundaryRows
import LocalLaw.DetachedEndpointRows
import LocalLaw.SourceEndpointMatrices
import LocalLaw.EndpointPostCross

/-! # Exact preservation of the relabelled finite boundary Green block

Rejected boundary rows annihilate the actual perturbation. Accepted old
a-rows and new c-rows have the same scalar diagonal. The exact inverse
updates therefore prove boundary-block preservation, without graph matching.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2500000
namespace LocalLaw
local instance boundaryBlockPreservationDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace LabelledResamplingState
variable {V : Type} {T : Set V} {ι : Type} [Fintype ι]

omit [Fintype ι] in
theorem oldBoundaryRoot_eq_eligible_iff (s : LabelledResamplingState V T ι) (selector : ℕ)
    (i : s.AdmissibleSampleIndex selector) (j : ι) :
    s.endpointRootLabel selector (Sum.inl (s.boundary j)) =
      s.endpointRootLabel selector (Sum.inl (s.boundary i.val)) ↔ j = i.val := by
  constructor
  · intro he
    apply s.eligible_triple_index_unique selector i (boundaryOutsideVertex s.graph T (s.boundary i.val))
      (Or.inl rfl) j
    have hraw := congrArg (fun v : s.endpointModelRoots selector => v.val.val) he
    exact Or.inl hraw.symm
  · exact fun h => congrArg (fun j => s.endpointRootLabel selector (Sum.inl (s.boundary j))) h

omit [Fintype ι] in
theorem finalBoundaryRoot_eq_eligible_tip_iff (s : LabelledResamplingState V T ι) (selector : ℕ)
    (i : s.AdmissibleSampleIndex selector) (j : ι) :
    s.endpointFinalBoundaryRoot selector j = s.endpointTipRoot selector i ↔ j = i.val := by
  constructor
  · intro he
    apply s.eligible_triple_index_unique selector i (s.admissibleSecondVertex selector i)
      (Or.inr (Or.inr rfl)) j
    have hraw := congrArg (fun v : s.endpointModelRoots selector => v.val.val) he
    have hmem := s.endpointFinalBoundaryRoot_mem_triple selector j
    exact Eq.mp (congrArg (fun v => v ∈ (s.quad j).exterior) hraw) hmem
  · intro he
    subst j
    simp only [endpointFinalBoundaryRoot, dif_pos i.property]
    rfl

theorem endpointFinalBoundaryRoot_outer (s : LabelledResamplingState V T ι) (selector : ℕ) (j : ι) :
    (s.endpointFinalBoundaryRoot selector j).val =
      boundaryOutsideVertex (s.fullResample selector).graph T ((s.fullResample selector).boundary j) := by
  apply Subtype.ext
  rw [show (boundaryOutsideVertex (s.fullResample selector).graph T
    ((s.fullResample selector).boundary j)).val = ((s.fullResample selector).boundary j).val.2 from rfl,
    s.fullResample_boundary_outer selector j]
  unfold endpointFinalBoundaryRoot
  split_ifs <;> rfl

end LabelledResamplingState

namespace RegularGraph
variable {N d : ℕ} {ι : Type} [Fintype ι]

omit [Fintype ι] in
theorem sourceEndpointP_rejected_support_zero (g : RegularGraph N d) (hd : 3 ≤ d)
    (T : Set (Fin N)) (boundary : ι ≃ BoundaryOrientedEdge g.graph T) (S : LocalSamplingFiber g.graph T)
    (selector r : ℕ) (hsep : 2 * r + 2 ≤ selector) (j : ι)
    (hj : ¬(g.admissibleState T boundary S).Eligible selector j)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (k : (g.admissibleState T boundary S).endpointModelRoots selector)
    (hk : k.val ∈ (g.admissibleState T boundary S).fullResampleOutsideEndpoints selector) :
    let s := g.admissibleState T boundary S
    g.sourceEndpointP T boundary S selector r q z (s.endpointRootLabel selector (Sum.inl (boundary j))) k = 0 := by
  dsimp only
  let s := g.admissibleState T boundary S
  let M := g.endpointModel T boundary S selector r
  let e := s.endpointModelKernelEmbedding selector r
  obtain ⟨a, ha, hk⟩ := hk
  let i : s.AdmissibleSampleIndex selector := ⟨a, ha⟩
  simp only [SwitchingQuad.exterior, Set.mem_insert_iff, Set.mem_singleton_iff] at hk
  rcases hk with hk | hk | hk
  · have he : k = s.endpointRootLabel selector (Sum.inl (boundary a)) :=
      Subtype.ext (Subtype.ext hk)
    rw [he]
    change M.extensionGreen q z (e (s.endpointRootLabel selector (Sum.inl (boundary j))))
      (e (s.endpointRootLabel selector (Sum.inl (boundary a)))) = 0
    rw [(M.extensionGreen_isSymm q z).apply]
    have hne : s.endpointRootLabel selector (Sum.inl (boundary j)) ≠
        s.endpointRootLabel selector (Sum.inl (boundary i.val)) := by
      intro heq
      exact hj (((s.oldBoundaryRoot_eq_eligible_iff selector i j).mp heq) ▸ i.property)
    have hrow := g.endpointModel_accepted_boundary_endpoint_row hd T boundary S selector r hsep i q z hz hq
      (s.endpointRootLabel selector (Sum.inl (boundary j)))
    dsimp only at hrow
    rw [if_neg hne] at hrow
    exact hrow
  · have he : k.val = s.admissibleSampleVertex selector i := Subtype.ext hk
    have hp : (e k).val ∈ s.sampledEndpointPatch selector r i := by
      change k.val ∈ s.sampledEndpointPatch selector r i
      rw [he]
      exact (s.sampledPatchFirst selector r i).property
    exact (g.endpointModel_boundary_sampledPatch_cross_zero hd T boundary S selector r hsep i
      (boundary j) (e k) hp q z hz hq).1
  · have he : k.val = s.admissibleSecondVertex selector i := Subtype.ext hk
    have hp : (e k).val ∈ s.sampledEndpointPatch selector r i := by
      change k.val ∈ s.sampledEndpointPatch selector r i
      rw [he]
      exact (s.sampledPatchSecond selector r i).property
    exact (g.endpointModel_boundary_sampledPatch_cross_zero hd T boundary S selector r hsep i
      (boundary j) (e k) hp q z hz hq).1

theorem sourceEndpointQ_rejected_row_eq (g : RegularGraph N d) (hd : 3 ≤ d)
    (T : Set (Fin N)) (boundary : ι ≃ BoundaryOrientedEdge g.graph T) (S : LocalSamplingFiber g.graph T)
    (selector r : ℕ) (hsep : 2 * r + 2 ≤ selector) (j : ι)
    (hj : ¬(g.admissibleState T boundary S).Eligible selector j)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im)
    (v : (g.admissibleState T boundary S).endpointModelRoots selector) :
    let s := g.admissibleState T boundary S
    g.sourceEndpointQ T boundary S selector r q z (s.endpointRootLabel selector (Sum.inl (boundary j))) v =
      g.sourceEndpointP T boundary S selector r q z (s.endpointRootLabel selector (Sum.inl (boundary j))) v := by
  dsimp only
  let s := g.admissibleState T boundary S
  let P := g.sourceEndpointP T boundary S selector r q z
  let Q := g.sourceEndpointQ T boundary S selector r q z
  let W := g.sourceEndpointW T boundary S selector
  let a := s.endpointRootLabel selector (Sum.inl (boundary j))
  have hPW : ∀ l, (P * W) a l = 0 := by
    intro l
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : k.val ∈ s.fullResampleOutsideEndpoints selector
    · exact mul_eq_zero_of_left (g.sourceEndpointP_rejected_support_zero hd T boundary S selector r hsep
        j hj q z hz hq k hk) _
    · have hagree := s.fullResample_outside_adj_of_away_left selector k.val l.val hk
      have hW : W k l = 0 := by
        change (normalizedAdjacency (outsideGraph (s.fullResample selector).graph T) d -
          normalizedAdjacency (outsideGraph s.graph T) d) k.val l.val = 0
        simp only [normalizedAdjacency, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, SimpleGraph.adjMatrix_apply]
        rw [hagree, sub_self]
      exact mul_eq_zero_of_right _ hW
  have hPWQ : (P * W * Q) a v = 0 := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    rw [hPW, zero_mul]
  have h := (g.source_endpoint_updates hd T boundary S selector r q z hz hq).2.2.1
  have he := congrFun (congrFun h a) v
  change Q a v + (P * W * Q) a v = P a v at he
  rw [hPWQ, add_zero] at he
  exact he

theorem sourceEndpoint_boundary_block_accepted (g : RegularGraph N d) (hd : 3 ≤ d)
    (T : Set (Fin N)) (boundary : ι ≃ BoundaryOrientedEdge g.graph T) (S : LocalSamplingFiber g.graph T)
    (selector r : ℕ) (hsep : 2 * r + 2 ≤ selector) (hr : r + 2 ≤ selector)
    (i : (g.admissibleState T boundary S).AdmissibleSampleIndex selector) (j : ι)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    let s := g.admissibleState T boundary S
    g.sourceEndpointQ T boundary S selector r q z (s.endpointFinalBoundaryRoot selector i.val)
      (s.endpointFinalBoundaryRoot selector j) =
    g.sourceEndpointP T boundary S selector r q z (s.endpointRootLabel selector (Sum.inl (boundary i.val)))
      (s.endpointRootLabel selector (Sum.inl (boundary j))) := by
  dsimp only
  let s := g.admissibleState T boundary S
  have hi := (s.finalBoundaryRoot_eq_eligible_tip_iff selector i i.val).mpr rfl
  rw [hi]
  have hQ := g.switchedEndpointModel_tip_endpoint_row hd T boundary S selector r hsep hr i q z hz hq
    (s.endpointFinalBoundaryRoot selector j)
  have hP := g.endpointModel_accepted_boundary_endpoint_row hd T boundary S selector r hsep i q z hz hq
    (s.endpointRootLabel selector (Sum.inl (boundary j)))
  dsimp only at hQ hP
  by_cases hji : j = i.val
  · have hqe := (s.finalBoundaryRoot_eq_eligible_tip_iff selector i j).mpr hji
    have hpe : s.endpointRootLabel selector (Sum.inl (boundary j)) =
        (g.admissibleState T boundary S).endpointRootLabel selector (Sum.inl (boundary i.val)) :=
      (s.oldBoundaryRoot_eq_eligible_iff selector i j).mpr hji
    rw [if_pos hqe] at hQ
    rw [if_pos hpe] at hP
    exact hQ.trans hP.symm
  · have hqe := fun h => hji ((s.finalBoundaryRoot_eq_eligible_tip_iff selector i j).mp h)
    have hpe : s.endpointRootLabel selector (Sum.inl (boundary j)) ≠
        (g.admissibleState T boundary S).endpointRootLabel selector (Sum.inl (boundary i.val)) :=
      fun h => hji ((s.oldBoundaryRoot_eq_eligible_iff selector i j).mp h)
    rw [if_neg hqe] at hQ
    rw [if_neg hpe] at hP
    exact hQ.trans hP.symm

/-- The full relabelled finite boundary block is exactly unchanged by the
actual source resampling. It needs no reference-class or smallness input. -/
theorem sourceEndpoint_boundary_block_preserved (g : RegularGraph N d) (hd : 3 ≤ d)
    (T : Set (Fin N)) (boundary : ι ≃ BoundaryOrientedEdge g.graph T) (S : LocalSamplingFiber g.graph T)
    (selector r : ℕ) (hsep : 2 * r + 2 ≤ selector) (hr : r + 2 ≤ selector)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) (j k : ι) :
    let s := g.admissibleState T boundary S
    g.sourceEndpointQ T boundary S selector r q z (s.endpointFinalBoundaryRoot selector j)
      (s.endpointFinalBoundaryRoot selector k) =
    g.sourceEndpointP T boundary S selector r q z (s.endpointRootLabel selector (Sum.inl (boundary j)))
      (s.endpointRootLabel selector (Sum.inl (boundary k))) := by
  dsimp only
  let s := g.admissibleState T boundary S
  by_cases hj : s.Eligible selector j
  · exact g.sourceEndpoint_boundary_block_accepted hd T boundary S selector r hsep hr ⟨j, hj⟩ k q z hz hq
  · by_cases hk : s.Eligible selector k
    · have hs := g.sourceEndpoint_boundary_block_accepted hd T boundary S selector r hsep hr ⟨k, hk⟩ j q z hz hq
      dsimp only at hs
      have hQsym := ((g.switchedEndpointModel T boundary S selector r).extensionGreen_isSymm q z).submatrix
        (s.endpointModelKernelEmbedding selector r)
      have hPsym := ((g.endpointModel T boundary S selector r).extensionGreen_isSymm q z).submatrix
        (s.endpointModelKernelEmbedding selector r)
      exact (hQsym.apply _ _).trans (hs.trans (hPsym.apply _ _))
    · have hjf : s.endpointFinalBoundaryRoot selector j = s.endpointRootLabel selector (Sum.inl (boundary j)) := by
        simp only [LabelledResamplingState.endpointFinalBoundaryRoot, dif_neg hj]
        rfl
      have hkf : s.endpointFinalBoundaryRoot selector k = s.endpointRootLabel selector (Sum.inl (boundary k)) := by
        simp only [LabelledResamplingState.endpointFinalBoundaryRoot, dif_neg hk]
        rfl
      rw [hjf, hkf]
      exact g.sourceEndpointQ_rejected_row_eq hd T boundary S selector r hsep j hj q z hz hq
        (s.endpointRootLabel selector (Sum.inl (boundary k)))

end RegularGraph
end LocalLaw
