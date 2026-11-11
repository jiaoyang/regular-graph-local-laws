import LocalLaw.PartialRestoredRows
import LocalLaw.SourcePartialReferenceBounds

/-! # Deficit-restored partial boundary rows at the actual old Q

Restoration is performed on the actual deficient graph at q itself. The
intrinsic diameter and finite-class feedback are inherited, so separated
kernel decay yields a row constant without any Lipschitz-times-cardinality
loss.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1800000
namespace LocalLaw
local instance restoredBoundaryQDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace DeficientGraph
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I] {d : ℕ}

theorem separated_perturbed_endpoint_rows (g : DeficientGraph V d) (hd : 3≤d)
    (hbudget : g.ComponentFiniteReferenceBudget) (e : I↪V) (h : ℕ)
    (hsep : ∀ i j,i≠j→(h:ℕ∞)≤g.graph.edist (e i) (e j))
    (z q : ℂ) (hz : 0<z.im) (hq : 0≤q.im) (R : ℕ) (hR : ∀i j,g.graph.dist i j≤R)
    (small : ‖q-semicircleRoot z‖*finiteExtraReferenceConstant d*
      coreConvolutionConstant (finiteOmega d+1)*((R:ℝ)+1)≤1/2)
    (hsmall : (Fintype.card I:ℝ)*physicalTransfer d z^h≤1) :
    (∀ i,∑ j,‖g.extensionGreen q z (e i) (e j)‖≤4*finiteExtraReferenceConstant d) ∧
      (∀ j,∑ i,‖g.extensionGreen q z (e i) (e j)‖≤4*finiteExtraReferenceConstant d) := by
  let C:=2*finiteExtraReferenceConstant d
  let t:=physicalTransfer d z
  have hC : 0≤C := by dsimp only [C]; have hc:=finiteExtraReferenceConstant_ge_one d hd; positivity
  have ht : 0≤t := (physicalTransfer_pos d hd z).le
  have htOne : t≤1 := by dsimp only [t]; nlinarith [physicalTransfer_sq_le_half d hd z]
  have hk:=g.componentwise_finite_kernel_decay hd hbudget q z hz hq R hR small
  have hcap (i j:I) : ‖g.extensionGreen q z (e i) (e j)‖≤C :=
    (hk (e i) (e j)).trans (mul_le_of_le_one_right hC (pow_le_one₀ ht htOne))
  have hfar (i j:I) (hij:i≠j) : ‖g.extensionGreen q z (e i) (e j)‖≤C*t^h := by
    by_cases hr:g.graph.Reachable (e i) (e j)
    · have heq : (g.graph.dist (e i) (e j):ℕ∞)=g.graph.edist (e i) (e j) :=
        ENat.coe_toNat (SimpleGraph.edist_ne_top_iff_reachable.mpr hr)
      have hdist : h≤g.graph.dist (e i) (e j) := ENat.coe_le_coe.mp ((hsep i j hij).trans_eq heq.symm)
      exact (hk (e i) (e j)).trans (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one ht htOne hdist) hC)
    · let c:=g.graph.connectedComponentMk (e i)
      have hj:e j∉c.supp := fun hh=>hr (SimpleGraph.ConnectedComponent.exact hh.symm)
      rw [g.extensionGreen_zero_across_cut hd c.supp (g.component_cut c) q z hz hq _ rfl _ hj,norm_zero]
      positivity
  have hrow (i:I) : ∑j,‖g.extensionGreen q z (e i) (e j)‖≤4*finiteExtraReferenceConstant d := by
    have hp (j:I) : ‖g.extensionGreen q z (e i) (e j)‖≤(if j=i then C else 0)+C*t^h := by
      by_cases hij:j=i
      · simpa only [hij,if_true] using (hcap i i).trans (le_add_of_nonneg_right (mul_nonneg hC (pow_nonneg ht _)))
      · simpa only [hij,if_false,zero_add] using hfar i j (Ne.symm hij)
    have hh : (∑j,‖g.extensionGreen q z (e i) (e j)‖)≤C+(Fintype.card I:ℝ)*(C*t^h) :=
      (Finset.sum_le_sum (fun j _=>hp j)).trans_eq (by simp [Finset.sum_add_distrib])
    have hs:=mul_le_mul_of_nonneg_left hsmall hC
    dsimp only [C] at hh hs
    nlinarith only [hh,hs]
  refine ⟨hrow,fun j=>?_⟩
  have hs:=g.extensionGreen_isSymm q z
  have heq : (∑i,‖g.extensionGreen q z (e i) (e j)‖)=∑i,‖g.extensionGreen q z (e j) (e i)‖ :=
    Finset.sum_congr rfl (fun i _=>congrArg norm (hs.apply (e j) (e i)))
  rw [heq]
  exact hrow j

theorem restored_perturbed_block_rows (g : DeficientGraph V d) (hd : 3≤d)
    (hbudget : g.ComponentFiniteReferenceBudget) (e : I↪V)
    (hA : ∀v∈Set.range e,0<g.deficit v) (h : ℕ)
    (hsep : ∀i j,i≠j→(h:ℕ∞)≤g.graph.edist (e i) (e j))
    (z q : ℂ) (hz : 0<z.im) (hq : 0≤q.im) (R : ℕ) (hR : ∀i j,g.graph.dist i j≤R)
    (small : ‖q-semicircleRoot z‖*finiteExtraReferenceConstant d*
      coreConvolutionConstant (finiteOmega d+1)*((R:ℝ)+1)≤1/2)
    (hsmall : (Fintype.card I:ℝ)*physicalTransfer d z^h≤1) :
    let P:=((g.extensionGreen q z).submatrix e e)⁻¹-
      q•Matrix.diagonal (fun _:I=>((1/((d:ℝ)-1):ℝ):ℂ))
    IsUnit P ∧ (∀i,∑j,‖P⁻¹ i j‖≤4*finiteExtraReferenceConstant d) ∧
      (∀j,∑i,‖P⁻¹ i j‖≤4*finiteExtraReferenceConstant d) := by
  dsimp only
  let gnew:=g.restoreOneDeficit (Set.range e) hA
  have hb:=g.restoreOneDeficit_componentFiniteReferenceBudget (Set.range e) hA hbudget
  have hrows:=gnew.separated_perturbed_endpoint_rows hd hb e h hsep z q hz hq R hR small hsmall
  have he:=g.restoreOneDeficit_embedding_Green hd e hA q z hz hq
  have hi:=g.restoreOneDeficit_embedding_inverse hd e hA q z hz hq
  refine ⟨?_,?_,?_⟩
  · rw [←hi.2.2]
    exact Matrix.isUnit_nonsing_inv_iff.mpr hi.2.1
  · intro i
    have hh:=hrows.1 i
    change (∑j,‖((gnew.extensionGreen q z).submatrix e e) i j‖)≤_ at hh
    rw [he] at hh
    exact hh
  · intro j
    have hh:=hrows.2 j
    change (∑i,‖((gnew.extensionGreen q z).submatrix e e) i j‖)≤_ at hh
    rw [he] at hh
    exact hh

end DeficientGraph
namespace RegularGraph
variable {N d : ℕ} {ι : Type} [Fintype ι]

theorem partial_restored_boundary_q_rows (g : RegularGraph N d) (hd : 3≤d)
    (T:Set (Fin N))(labels:ι≃BoundaryOrientedEdge g.graph T)(samples:LocalSamplingFiber g.graph T)
    (selector:ℕ)(S:Set (Tᶜ:Set (Fin N)))
    (hb:((g.deficient.delete T).restrict S).ComponentFiniteReferenceBudget)
    (z q:ℂ)(hz:0<z.im)(hq:0≤q.im)(R:ℕ)
    (hR:∀i j,((g.deficient.delete T).restrict S).graph.dist i j≤R)
    (small:‖q-semicircleRoot z‖*finiteExtraReferenceConstant d*
      coreConvolutionConstant (finiteOmega d+1)*((R:ℝ)+1)≤1/2)
    (hsmall:(Fintype.card ((g.admissibleState T labels samples).partialBoundaryMask selector S):ℝ)*
      physicalTransfer d z^selector≤1) :
    let s:=g.admissibleState T labels samples
    let e:=s.partialBoundaryEmbedding selector S
    let P:=(((g.deficient.delete T).restrict S).extensionGreen q z).submatrix e e
    let K:=P⁻¹-Matrix.diagonal (fun _:s.partialBoundaryMask selector S=>q*treeEdgeWeight d^2)
    IsUnit K ∧ (∀i,∑j,‖K⁻¹ i j‖≤4*finiteExtraReferenceConstant d) ∧
      (∀j,∑i,‖K⁻¹ i j‖≤4*finiteExtraReferenceConstant d) := by
  dsimp only
  let s:=g.admissibleState T labels samples
  let e:=s.partialBoundaryEmbedding selector S
  let M:=(g.deficient.delete T).restrict S
  let A:=s.partialBoundaryMask selector S
  have hpos : ∀v∈Set.range e,0<M.deficit v := by
    intro v hv
    have hi:v∈s.includedEligibleBoundary selector S := s.partialBoundaryEmbedding_range selector S ▸ hv
    change 0<((g.deficient.delete T).restrict S).deficit v
    rw [g.includedEligibleBoundary_deficit_one T labels samples selector S v hi]
    norm_num
  have hsep (i j:A)(hij:i≠j) : (selector:ℕ∞)≤M.graph.edist (e i) (e j) :=
    (s.partialBoundaryEmbedding_separated selector S i j hij).le.trans
      (graphHom_edist_le (SimpleGraph.Embedding.induce (G:=outsideGraph g.graph T) S).toHom (e i) (e j))
  have hh:=M.restored_perturbed_block_rows hd hb e hpos selector hsep z q hz hq R hR small hsmall
  have hcast : ((1/((d:ℝ)-1):ℝ):ℂ)=(1:ℂ)/((d:ℂ)-1) := by push_cast; rfl
  have hD : Matrix.diagonal (fun _:A=>q*treeEdgeWeight d^2)=
      q•Matrix.diagonal (fun _:A=>((1/((d:ℝ)-1):ℝ):ℂ)) := by
    ext i j
    by_cases hij:i=j
    · subst j
      simp only [Matrix.diagonal_apply_eq,Matrix.smul_apply,smul_eq_mul,treeEdgeWeight_sq d hd,hcast]
    · simp [Matrix.diagonal_apply,hij]
  rw [hD]
  exact hh

end RegularGraph
end LocalLaw
