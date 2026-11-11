import LocalLaw.LeafSchurModel

/-! # Literal precision blocks for arbitrary deficit-restoring leaves -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance attachedLeafBlocksDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace DeficientGraph
variable {V I:Type} [Fintype V] [Fintype I] {d:ℕ}

theorem attachLeaves_extensionMatrix_core_leaf (g:DeficientGraph V d)(hd:3≤d)
    (mate:I→V)(hr:∀v,multiLeafMultiplicity mate v≤g.deficit v)(q z:ℂ)(v:V)(l:I) :
    (g.attachLeaves (by omega) mate hr).extensionMatrix q z (.inl v) (.inr l)=
      if v=mate l then treeEdgeWeight d else 0 := by
  simp only [extensionMatrix,boundaryMatrix,spectralMatrix,H,normalizedAdjacency,
    boundaryDiagonal,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,
    Matrix.diagonal_apply,Sum.inl_ne_inr,if_false,mul_zero,sub_zero,
    attachLeaves,multiLeafGraph,SimpleGraph.adjMatrix_apply]
  by_cases hv:v=mate l <;> simp [hv,treeEdgeWeight,Complex.ofReal_inv]

theorem attachLeaves_extensionMatrix_leaf (g:DeficientGraph V d)(hd:3≤d)
    (mate:I→V)(hr:∀v,multiLeafMultiplicity mate v≤g.deficit v)(q z:ℂ)(l k:I) :
    (g.attachLeaves (by omega) mate hr).extensionMatrix q z (.inr l) (.inr k)=
      if l=k then -z-q else 0 := by
  let Mdl:=g.attachLeaves (by omega) mate hr
  have hD:Mdl.boundaryCoefficient (.inr l)=1:=by
    have hdR:(3:ℝ)≤d:=Nat.cast_le.mpr hd
    have hk:((d:ℝ)-1)≠0:=by linarith
    simp only [Mdl,boundaryCoefficient,attachLeaves,Sum.elim_inr,Nat.cast_zero,sub_zero]
    change ((d:ℝ)-(multiLeafGraph g.graph mate).degree (.inr l))/((d:ℝ)-1)=1
    rw [multiLeafGraph_degree_leaf]
    push_cast
    field_simp
  change Mdl.extensionMatrix q z (.inr l) (.inr k)=_
  have hAdj:¬Mdl.graph.Adj (.inr l) (.inr k):=by
    change ¬False
    exact not_false
  have hH:Mdl.H (.inr l) (.inr k)=0:=by
    simp only [DeficientGraph.H,normalizedAdjacency,Matrix.smul_apply,smul_eq_mul,
      SimpleGraph.adjMatrix_apply,if_neg hAdj,mul_zero]
  simp only [extensionMatrix,boundaryMatrix,spectralMatrix,boundaryDiagonal,
    Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,
    Matrix.diagonal_apply,Sum.inr.injEq,hH,hD,Complex.ofReal_one]
  by_cases hl:l=k <;> simp [hl]

theorem attachLeaves_leaf_inverse_precision (g:DeficientGraph V d)(hd:3≤d)
    (mate:I→V)(hr:∀v,multiLeafMultiplicity mate v≤g.deficit v)(q z:ℂ)
    (hz:0<z.im)(hq:0≤q.im) :
    (((g.attachLeaves (by omega) mate hr).extensionGreen q z).submatrix Sum.inr Sum.inr)⁻¹=
      Matrix.diagonal (fun _:I=>-z-q)-
        (treeEdgeWeight d)^2 • (g.extensionGreen q z).submatrix mate mate := by
  let Mdl:=g.attachLeaves (by omega) mate hr
  let M:=Mdl.extensionMatrix q z
  have hM:IsUnit M:=Mdl.extensionMatrix_isUnit hd q z hz hq
  have hcore:M.toBlocks₁₁=g.extensionMatrix q z:=by
    exact g.attachLeaves_extensionMatrix_principal (by omega) mate hr q z
  have hcu:IsUnit M.toBlocks₁₁:=hcore ▸ g.extensionMatrix_isUnit hd q z hz hq
  have hi:=inverse_block22 M hM hcu
  change (M⁻¹).toBlocks₂₂⁻¹=_
  rw [hi.2,Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hi.1)]
  ext l k
  simp only [Matrix.sub_apply,Matrix.diagonal_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.mul_apply,Matrix.toBlocks₂₂,Matrix.toBlocks₂₁,Matrix.toBlocks₁₂,Matrix.submatrix_apply,Matrix.of_apply]
  have hc1 (v:V):M (.inl v) (.inr k)=if v=mate k then treeEdgeWeight d else 0:=
    g.attachLeaves_extensionMatrix_core_leaf hd mate hr q z v k
  have hc2 (v:V):M (.inr l) (.inl v)=if v=mate l then treeEdgeWeight d else 0:=by
    dsimp only [M,Mdl]
    simp only [extensionMatrix,boundaryMatrix,spectralMatrix,DeficientGraph.H,normalizedAdjacency,
      boundaryDiagonal,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,
      Matrix.diagonal_apply,Sum.inr_ne_inl,if_false,mul_zero,sub_zero,
      attachLeaves,multiLeafGraph,SimpleGraph.adjMatrix_apply]
    by_cases hv:v=mate l <;> simp [hv,treeEdgeWeight,Complex.ofReal_inv]
  have hdiag:M (.inr l) (.inr k)=(if l=k then -z-q else 0):=
    g.attachLeaves_extensionMatrix_leaf hd mate hr q z l k
  rw [hdiag]
  simp_rw [hc1,hc2]
  rw [hcore]
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true,
    ite_mul,zero_mul,Finset.sum_ite_eq]
  change (if l=k then -z-q else 0)-treeEdgeWeight d*g.extensionGreen q z (mate l) (mate k)*treeEdgeWeight d=_
  ring

end DeficientGraph
end LocalLaw
