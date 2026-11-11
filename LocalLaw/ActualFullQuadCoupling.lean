import LocalLaw.FullEndpointCoordinates
import LocalLaw.FullRetainedPrecision
import LocalLaw.FullQuadRowCharges
import LocalLaw.FullSwitchRows

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance actualFullQuadMatrixDecidable (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 3000000
namespace LabelledResamplingState
variable {V : Type} [Fintype V] {T : Set V} {ι : Type} [Fintype ι]

omit [Fintype V] in
theorem full_core_core_edge_update (s : LabelledResamplingState V T ι)
    (selector : ℕ) (hs : 1 ≤ selector) (S : Set V) (α : ℂ)
    (k k' : s.fullCoreMask S) :
    α * ((if (s.fullResample selector).graph.Adj k.val k'.val then (1 : ℂ) else 0) -
      (if s.graph.Adj k.val k'.val then 1 else 0)) =
      -fullQuadRetainedEdges (s.fullInnerMate selector S) (s.fullOuterMate selector S) α k k' := by
  rw [s.fullResample_signed_edge_sum selector, Finset.mul_sum]
  unfold fullQuadRetainedEdges
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hkB : k.val ≠ (s.quad i.val).c := s.fullCore_ne_inner_sample selector S k i
  have hkC : k.val ≠ (s.quad i.val).d := s.fullCore_ne_second_sample selector hs S k i
  have hk'B : k'.val ≠ (s.quad i.val).c := s.fullCore_ne_inner_sample selector S k' i
  have hk'C : k'.val ≠ (s.quad i.val).d := s.fullCore_ne_second_sample selector hs S k' i
  have ha := sampledSwitching_admissible s.graph T selector s.samples (s.boundary i.val) i.property.1 i.property.2
  have hab : (s.quad i.val).a ≠ (s.quad i.val).b := ha.ab_ne
  have hout : (s.admissibleBoundaryVertex selector i).val = (s.quad i.val).b := rfl
  simp only [s.fullInnerMate_eq_some, s.fullOuterMate_eq_some, switchingAdded,
    switchingRemoved, SimpleGraph.sup_adj, SimpleGraph.edge_adj, hout,
    hkB, hkC, hk'B, hk'C, false_and, and_false, or_false, false_or,
    if_false, zero_sub]
  by_cases hxy : k.val = k'.val
  · have hkk : k = k' := Subtype.ext hxy
    subst k'
    simp only [ne_eq, not_true_eq_false, and_false, if_false, mul_zero]
    split_ifs with h1 h2 <;> (try ring_nf) <;> exfalso <;> aesop
  · try simp only [hxy, not_false_eq_true, and_true]
    split_ifs <;> (try ring_nf) <;> exfalso <;> aesop

def fullSignedEdgeBlock (s : LabelledResamplingState V T ι)
    (selector : ℕ) (S : Set V) (hs : 1 ≤ selector) (α : ℂ) :
    Matrix (s.FullEndpointIndex selector S) (s.FullEndpointIndex selector S) ℂ :=
  fun u v => α * ((if (s.fullResample selector).graph.Adj
      (s.fullPartialEmbedding selector S hs u).val (s.fullPartialEmbedding selector S hs v).val then 1 else 0) -
    (if s.graph.Adj (s.fullPartialEmbedding selector S hs u).val
      (s.fullPartialEmbedding selector S hs v).val then 1 else 0))

omit [Fintype V] in
theorem fullSignedEdgeBlock_eq (s : LabelledResamplingState V T ι)
    (selector : ℕ) (S : Set V) (hs : 1 ≤ selector) (α : ℂ) :
    s.fullSignedEdgeBlock selector S hs α =
      fullQuadSurgeryCoupling (s.fullInnerMate selector S) (s.fullOuterMate selector S)
        (s.fullFirstMask selector S) (s.fullSecondMask selector S) 0 α := by
  have hboundary (i : s.AdmissibleSampleIndex selector) :
      (s.admissibleBoundaryVertex selector i).val = (s.quad i.val).b := rfl
  have hfirst (i : s.AdmissibleSampleIndex selector) :
      (s.quad i.val).c = (s.admissibleSampleVertex selector i).val := rfl
  have hsecond (i : s.AdmissibleSampleIndex selector) :
      (s.quad i.val).d = (s.admissibleSecondVertex selector i).val := rfl
  ext u v
  rcases u with k | (b | c) <;> rcases v with k' | (b' | c')
  all_goals simp only [fullSignedEdgeBlock,fullPartialEmbedding,Function.Embedding.coeFn_mk,
    fullPartialVertex,fullCoreEmbedding,fullQuadSurgeryCoupling,fullQuadSampleCharge,
    Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂,Matrix.sub_apply,Matrix.neg_apply,Matrix.transpose_apply,
    zero_mul,Matrix.diagonal_zero,Matrix.zero_apply,sub_zero,
    vacuumLeafIncidence,fullQuadLeafMate]
  · exact s.full_core_core_edge_update selector hs S α k k'
  · simp_rw [(s.fullResample selector).graph.adj_comm k.val (s.admissibleSampleVertex selector b'.val).val,
      s.graph.adj_comm k.val (s.admissibleSampleVertex selector b'.val).val]
    rw [s.full_first_indicator_difference selector b'.val]
    simp only [s.fullOuterMate_eq_some,hboundary]
    have hnot : k.val ≠ (s.quad b'.val.val).d := s.fullCore_ne_second_sample selector hs S k b'.val
    simp only [hnot,if_false,sub_zero]
    by_cases he : k.val = (s.quad b'.val.val).b
    · simp [he]
    · simp [he,Ne.symm he]
  · simp_rw [(s.fullResample selector).graph.adj_comm k.val (s.admissibleSecondVertex selector c'.val).val,
      s.graph.adj_comm k.val (s.admissibleSecondVertex selector c'.val).val]
    rw [s.full_second_indicator_difference selector c'.val]
    simp only [s.fullInnerMate_eq_some]
    have hnot : k.val ≠ (s.quad c'.val.val).c := s.fullCore_ne_inner_sample selector S k c'.val
    simp only [hnot,if_false,sub_zero]
    by_cases he : k.val = (s.quad c'.val.val).a
    · simp [he]
    · simp [he,Ne.symm he]
  · rw [s.full_first_indicator_difference selector b.val]
    simp only [s.fullOuterMate_eq_some,hboundary]
    have hnot : k'.val ≠ (s.quad b.val.val).d := s.fullCore_ne_second_sample selector hs S k' b.val
    simp only [hnot,if_false,sub_zero]
    by_cases he : k'.val = (s.quad b.val.val).b
    · simp [he]
    · simp [he,Ne.symm he]
  · rw [s.full_first_indicator_difference selector b.val]
    simp [s.full_first_outer_ne, hsecond, s.full_first_second_ne]
  · rw [s.full_first_indicator_difference selector b.val]
    simp only [s.full_second_outer_ne selector hs,if_false,zero_sub,hsecond,
      s.full_second_second_eq,partialMatchingCoupling]
    split_ifs <;> simp_all only [eq_comm, if_true, if_false, not_true_eq_false, not_false_eq_true] <;> ring
  · rw [s.full_second_indicator_difference selector c.val]
    simp only [s.fullInnerMate_eq_some]
    have hnot : k'.val ≠ (s.quad c.val.val).c := s.fullCore_ne_inner_sample selector S k' c.val
    simp only [hnot,if_false,sub_zero]
    by_cases he : k'.val = (s.quad c.val.val).a
    · simp [he]
    · simp [he,Ne.symm he]
  · rw [s.full_second_indicator_difference selector c.val]
    simp only [s.full_first_inner_ne,if_false,zero_sub,hfirst,
      s.full_first_first_eq,partialMatchingCoupling]
    split_ifs <;> simp_all only [eq_comm, if_true, if_false, not_true_eq_false, not_false_eq_true] <;> ring
  · rw [s.full_second_indicator_difference selector c.val]
    simp [s.full_second_inner_ne,hfirst,Ne.symm (s.full_first_second_ne selector _ _)]

end LabelledResamplingState
namespace RegularGraph
variable {N d : ℕ} {ι : Type} [Fintype ι]

/-- The actual retained full precision is exactly the generic full-quad update. -/
theorem full_partial_retained_quad_precision (g : RegularGraph N d) (hd : 3 ≤ d)
    (T : Set (Fin N)) (labels : ι ≃ BoundaryOrientedEdge g.graph T)
    (samples : LocalSamplingFiber g.graph T) (selector : ℕ) (hs : 1 ≤ selector)
    (S : Set (Fin N)) (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    let s := g.admissibleState T labels samples
    let h := g.labelledResampledGraph T labels samples selector
    let e := s.fullPartialEmbedding selector S hs
    let R := ((g.deficient.restrict S).extensionGreen q z).submatrix e e
    let U := ((h.deficient.restrict S).extensionGreen q z).submatrix e e
    let W : Matrix (s.FullEndpointIndex selector S) (s.FullEndpointIndex selector S) ℂ :=
      fullQuadSurgeryCoupling (s.fullInnerMate selector S) (s.fullOuterMate selector S)
        (s.fullFirstMask selector S) (s.fullSecondMask selector S) q (treeEdgeWeight d)
    IsUnit R ∧ IsUnit U ∧ U⁻¹ = R⁻¹ + W := by
  dsimp only
  let s := g.admissibleState T labels samples
  let h := g.labelledResampledGraph T labels samples selector
  let e := s.fullPartialEmbedding selector S hs
  let f : s.FullEndpointIndex selector S ↪ Fin N :=
    ⟨fun u => (e u).val,fun _ _ he => e.injective (Subtype.ext he)⟩
  have hh := g.full_partial_retained_precision hd T labels samples selector hs S q z hz hq
  have hD : (h.H - g.H).submatrix f f = s.fullSignedEdgeBlock selector S hs (treeEdgeWeight d) := by
    ext u v
    simp only [Matrix.submatrix_apply,H,normalizedAdjacency,Matrix.sub_apply,
      Matrix.smul_apply,smul_eq_mul,SimpleGraph.adjMatrix_apply,
      LabelledResamplingState.fullSignedEdgeBlock,treeEdgeWeight]
    have hg : h.graph = (s.fullResample selector).graph := rfl
    have ho : g.graph = s.graph := rfl
    dsimp only [f,e]
    simp only [Function.Embedding.coeFn_mk]
    rw [hg,ho]
    ring
  dsimp only at hh
  refine ⟨hh.1,hh.2.1,?_⟩
  rw [hh.2.2]
  have he := s.fullSignedEdgeBlock_eq selector S hs (treeEdgeWeight d)
  change (h.H-g.H).submatrix f f = _ at hD
  rw [hD,he,add_assoc]
  congr 1
  have hcanonical : instDecidableEqFin N =
      (fun a b : Fin N => actualFullQuadMatrixDecidable (a = b)) := Subsingleton.elim _ _
  rw [hcanonical]
  have hc := fullQuadSurgery_row_charge (s.fullInnerMate selector S) (s.fullOuterMate selector S)
    (s.fullFirstMask selector S) (s.fullSecondMask selector S) q (treeEdgeWeight d)
  simp only [hcanonical] at hc
  refine Eq.trans ?_ hc.symm
  congr 1
  congr 1
  ext i j
  by_cases hij : i = j
  · simp only [Matrix.diagonal_apply,hij,if_true]
    simp only [← finsum_eq_sum_of_fintype]
    exact finsum_comp_equiv
      (show s.FullEndpointIndex selector S ≃
        (s.fullCoreMask S ⊕ (s.fullFirstMask selector S ⊕ s.fullSecondMask selector S)) from Equiv.refl _)
  · simp only [Matrix.diagonal_apply,hij,if_false]

end RegularGraph
end LocalLaw
