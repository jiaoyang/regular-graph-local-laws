import LocalLaw.CoreAttachments
import LocalLaw.GoodSampleEvenPatterns
import LocalLaw.RejectedSwitchingCounts
import LocalLaw.ResamplingCollisionGeometry

/-! All-label large tree patches, with an actual finite sampling probability. -/
open scoped BigOperators
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance largePatchSamplingDecidable (p:Prop):Decidable p:=Classical.propDecidable p

/-- Every sampled tree patch is far from the old cut and from every other
sampled patch. This event is stronger than the fixed-selector acceptance test. -/
def AllLargeSampleGood {V:Type*}[Fintype V](G:SimpleGraph V)(T:Set V)(M:ℕ)
    (S:LocalSamplingFiber G T):Prop:=
  sampledBoundaryHitIndices G T M S=∅ ∧
    (∀i j:BoundaryOrientedEdge G T,i≠j→¬sampledEdgesClose G T M (S i) (S j)) ∧
    nonTreeSampledPairIndices G T M S=∅

variable {V:Type*}[Fintype V]

theorem allLargeSampleGood_other_empty (G:SimpleGraph V)(T:Set V)(M:ℕ)
    (S:LocalSamplingFiber G T)(hS:AllLargeSampleGood G T M S):
    sampledOtherTripleIndices G T M S=∅:=by
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro i hi
  have hh:=sampledOtherTripleIndices_subset G T M S hi
  rcases Finset.mem_union.mp hh with hmark|hcoll
  · rw [hS.1] at hmark
    exact Finset.not_mem_empty i hmark
  · obtain ⟨j,hj⟩:=((sampledEdgeCollisionGraph G T M S).mem_support).mp (Set.mem_toFinset.mp hcoll)
    change i≠j ∧ sampledEdgesClose G T M (S i) (S j) at hj
    exact hS.2.1 i j hj.1 hj.2

theorem allLargeSampleGood_rejected_empty (G:SimpleGraph V)(o:V)(ell selector R M:ℕ)
    (hsel:ell+1+selector≤R)(hM:2*selector+1≤M)
    (hTree:(graphBall G o R).IsTree)
    (S:LocalSamplingFiber G (graphBallVertices G o ell))
    (hS:AllLargeSampleGood G (graphBallVertices G o ell) M S):
    rejectedResamplingIndices G (graphBallVertices G o ell) selector S=∅:=by
  have hzero:graphBallExcess G o R≤0:=(tree_graphExcess_zero _ hTree).le
  have hboundary:=boundary_nonTree_ball_count G o ell R selector 0 hsel hzero
  have hhit:(sampledBoundaryHitIndices G (graphBallVertices G o ell) selector S).card≤0:=by
    have hh:=Finset.card_le_card (sampledBoundaryHitIndices_mono G _ (by omega:selector≤M) S)
    rw [hS.1,Finset.card_empty] at hh
    exact hh
  have hother:=boundaryOtherTripleIndices_card G o ell R selector 0 hsel hzero S
  have hr:=rejectedResamplingIndices_card_five_sets G o ell selector selector M le_rfl (by omega) hM S
  rw [hS.1,hS.2.2,allLargeSampleGood_other_empty G _ M S hS,Finset.card_empty] at hr
  have hc:(rejectedResamplingIndices G (graphBallVertices G o ell) selector S).card=0:=by omega
  exact Finset.card_eq_zero.mp hc

private theorem relation_exists_one_pair {I E:Type*}[Fintype I][Fintype E]
    (R:E→E→Prop)(f:I→E)(h:∃i j,i≠j ∧ R (f i) (f j)):
    ∃e:(Fin 1×Bool)↪I,DisjointPairConstraint R e f:=by
  obtain ⟨i,j,hij,hR⟩:=h
  let e:(Fin 1×Bool)↪I:={
    toFun:=fun p=>if p.2 then j else i
    inj':=by
      rintro ⟨a,b⟩ ⟨c,d⟩ hh
      have hac:a=c:=Subsingleton.elim _ _
      subst c
      have hbd:b=d:=by cases b <;> cases d <;> simp_all
      subst d
      rfl }
  refine ⟨e,?_⟩
  intro k
  exact hR

namespace RegularGraph
variable {N d:ℕ}

theorem localSampling_any_sample_collision (g:LocalLaw.RegularGraph N d)(T:Set (Fin N))
    (hN:0<N)(hd:3≤d)(hT:4*Nat.card T≤N)(M:ℕ):
    eventMass (localSamplingWeight g.graph T)
      (fun S=>∃i j:BoundaryOrientedEdge g.graph T,i≠j ∧ sampledEdgesClose g.graph T M (S i) (S j))≤
      (Nat.card (BoundaryOrientedEdge g.graph T):ℝ)^2*
        (8*(((d+1)*(d-1)^M:ℕ):ℝ)/(N:ℝ)):=by
  letI:Nonempty (OutsideOrientedEdge g.graph T):=g.outside_edge_nonempty T hN (by omega) hT
  let b:=4*d*((d+1)*(d-1)^M)
  have hh:=uniform_exists_disjointPairConstraint_tail (I:=BoundaryOrientedEdge g.graph T)
    (sampledEdgesClose g.graph T M) b 1 (fun e=>g.sampledEdgesClose_fiber_card T M hd e)
  have hden:(b:ℝ)/(Fintype.card (OutsideOrientedEdge g.graph T):ℝ)≤
      8*(((d+1)*(d-1)^M:ℕ):ℝ)/(N:ℝ):=by
    have hsize:=g.outside_edge_real_size T hT
    have hNp:0<(N:ℝ):=Nat.cast_pos.mpr hN
    have hEp:0<(Fintype.card (OutsideOrientedEdge g.graph T):ℝ):=Nat.cast_pos.mpr Fintype.card_pos
    apply (div_le_div_iff₀ hEp hNp).mpr
    have hmul:=mul_le_mul_of_nonneg_right hsize (by positivity:0≤8*(((d+1)*(d-1)^M:ℕ):ℝ))
    dsimp only [b]
    push_cast at hmul ⊢
    nlinarith
  apply (eventMass_mono (localSamplingWeight g.graph T) finiteUniformWeight_nonneg
    (fun S h=>relation_exists_one_pair _ S h)).trans
  apply hh.trans
  simpa only [pow_one,Nat.card_eq_fintype_card] using
    mul_le_mul_of_nonneg_left hden (sq_nonneg (Fintype.card (BoundaryOrientedEdge g.graph T):ℝ))

/-- No N-union occupancy loss is paid: only one deterministic-hit event,
one genuinely independent coordinate pair, and one sampled bad center. -/
theorem localSampling_allLargeSampleGood_failure (g:LocalLaw.RegularGraph N d)(T:Set (Fin N))
    (hN:0<N)(hd:3≤d)(hT:4*Nat.card T≤N)(M b:ℕ)
    (hbad:(nonTreeCenters g.graph (M+1)).card≤b):
    eventMass (localSamplingWeight g.graph T) (fun S=>¬AllLargeSampleGood g.graph T M S)≤
      12*(Nat.card (BoundaryOrientedEdge g.graph T):ℝ)^2*
        (((d+1)*(d-1)^M:ℕ):ℝ)/(N:ℝ)+
      4*(Nat.card (BoundaryOrientedEdge g.graph T):ℝ)*(b:ℝ)/(N:ℝ):=by
  let P:=fun S:LocalSamplingFiber g.graph T=>1≤(sampledBoundaryHitIndices g.graph T M S).card
  let Q:=fun S:LocalSamplingFiber g.graph T=>∃i j:BoundaryOrientedEdge g.graph T,i≠j ∧ sampledEdgesClose g.graph T M (S i) (S j)
  let U:=fun S:LocalSamplingFiber g.graph T=>1≤(nonTreeSampledPairIndices g.graph T M S).card
  have hcover:∀S,¬AllLargeSampleGood g.graph T M S→P S∨Q S∨U S:=by
    intro S hS
    by_cases hP:P S
    · exact Or.inl hP
    by_cases hQ:Q S
    · exact Or.inr (Or.inl hQ)
    by_cases hU:U S
    · exact Or.inr (Or.inr hU)
    apply False.elim
    apply hS
    refine ⟨Finset.card_eq_zero.mp (by dsimp only [P] at hP;omega),?_,
      Finset.card_eq_zero.mp (by dsimp only [U] at hU;omega)⟩
    intro i j hij hR
    exact hQ ⟨i,j,hij,hR⟩
  have hP:=g.localSampling_boundary_neighborhood_tail T hN hd hT M 1
  have hQ:=localSampling_any_sample_collision g T hN hd hT M
  have hU:=g.localSampling_nonTree_pair_tail T hN (by omega) hT M b 1 hbad
  have hu: eventMass (localSamplingWeight g.graph T) (fun S=>P S∨Q S∨U S)≤
      eventMass (localSamplingWeight g.graph T) P+
        (eventMass (localSamplingWeight g.graph T) Q+eventMass (localSamplingWeight g.graph T) U):=by
    exact (eventMass_union_le _ finiteUniformWeight_nonneg _ _).trans
      (add_le_add_left (eventMass_union_le _ finiteUniformWeight_nonneg _ _) _)
  apply ((eventMass_mono _ finiteUniformWeight_nonneg hcover).trans hu).trans
  have hh:=add_le_add hP (add_le_add hQ hU)
  convert hh using 1
  simp only [pow_one,P,Q,U]
  ring

end RegularGraph
end SpectralConsequences
#print axioms SpectralConsequences.RegularGraph.localSampling_allLargeSampleGood_failure
