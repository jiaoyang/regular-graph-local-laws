import LocalLaw.NormalizedLeafPrecision
import LocalLaw.AttachedLeafMatrixBlocks
import LocalLaw.DeficitReduction

/-! # Normalized leaf attachment is the actual restored-deficit model

The leaf diagonal q^-1 gives exactly the missing-neighbor self-energy.
Both the normalized full matrix and its core Schur complement are proved
nonsingular from the genuine restored deficient graph.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance normalizedLeafAttachmentDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace DeficientGraph
variable {V I:Type} [Fintype V] [Fintype I] {d:ℕ}

def normalizedLeafAttachment (g:DeficientGraph V d)(mate:I→V)(q z:ℂ):Matrix (V⊕I) (V⊕I) ℂ:=
  vacuumLeafMatrix (fun i=>some (mate i)) (g.extensionMatrix q z)
    (vacuumLeafMultiplicity (fun i=>some (mate i))) q q (treeEdgeWeight d)

theorem vacuumLeafMultiplicity_some (mate:I→V)(v:V) :
    vacuumLeafMultiplicity (fun i=>some (mate i)) v=(multiLeafMultiplicity mate v:ℂ) := by
  simp [vacuumLeafMultiplicity,multiLeafMultiplicity,Nat.card_eq_fintype_card,
    Fintype.card_subtype,Finset.sum_boole]

theorem normalizedLeafAttachment_core_precision (g:DeficientGraph V d)(hd:3≤d)
    (mate:I→V)(hr:∀v,multiLeafMultiplicity mate v≤g.deficit v)(q z:ℂ) :
    g.extensionMatrix q z-Matrix.diagonal
      (fun v=>q*(treeEdgeWeight d)^2*vacuumLeafMultiplicity (fun i=>some (mate i)) v)=
      (g.lowerDeficit (multiLeafMultiplicity mate) hr).extensionMatrix q z := by
  rw [g.lowerDeficit_extensionMatrix]
  congr 1
  ext v w
  by_cases hvw:v=w
  · subst w
    simp only [Matrix.diagonal_apply_eq,Matrix.smul_apply,smul_eq_mul,
      vacuumLeafMultiplicity_some,treeEdgeWeight_sq d hd]
    push_cast
    ring
  · simp [Matrix.diagonal_apply,hvw]

theorem normalizedLeafAttachment_unit_core (g:DeficientGraph V d)(hd:3≤d)
    (mate:I→V)(hr:∀v,multiLeafMultiplicity mate v≤g.deficit v)(q z:ℂ)
    (hq0:q≠0)(hz:0<z.im)(hq:0≤q.im) :
    IsUnit (g.normalizedLeafAttachment mate q z) ∧
      ((g.normalizedLeafAttachment mate q z)⁻¹).toBlocks₁₁=
        (g.lowerDeficit (multiLeafMultiplicity mate) hr).extensionGreen q z := by
  have he:=g.normalizedLeafAttachment_core_precision hd mate hr q z
  have hc:IsUnit (g.extensionMatrix q z-Matrix.diagonal
      (fun v=>q*(treeEdgeWeight d)^2*vacuumLeafMultiplicity (fun i=>some (mate i)) v)):=by
    rw [he]
    exact (g.lowerDeficit _ hr).extensionMatrix_isUnit hd q z hz hq
  have hh:=vacuumLeaf_schur (fun i=>some (mate i)) (g.extensionMatrix q z)
    (vacuumLeafMultiplicity (fun i=>some (mate i))) q q (treeEdgeWeight d) hq0 hq0 hc
  refine ⟨hh.1,?_⟩
  have hhc:=hh.2.2
  rw [he] at hhc
  exact hhc

theorem normalizedLeafAttachment_difference (g:DeficientGraph V d)(hd:3≤d)
    (mate:I→V)(hr:∀v,multiLeafMultiplicity mate v≤g.deficit v)(q z:ℂ)(hq0:q≠0) :
    g.normalizedLeafAttachment mate q z-(g.attachLeaves (by omega) mate hr).extensionMatrix q z=
      Matrix.diagonal (Sum.elim (fun _:V=>0) (fun _:I=>(1+z*q+q^2)/q)) := by
  let H:=g.attachLeaves (by omega) mate hr
  have hcore:((H.extensionMatrix q z).submatrix Sum.inl Sum.inl)=g.extensionMatrix q z:=
    g.attachLeaves_extensionMatrix_principal (by omega) mate hr q z
  ext a b
  rcases a with v|l <;> rcases b with w|k
  · have hh:=congrArg (fun M:Matrix V V ℂ=>M v w) hcore
    simp only [Matrix.submatrix_apply] at hh
    simp only [normalizedLeafAttachment,vacuumLeafMatrix,Matrix.sub_apply,
      Matrix.fromBlocks_apply₁₁,sub_self,mul_zero,Matrix.diagonal_zero,sub_zero,hh]
    simp only [Matrix.diagonal_apply,Sum.elim_inl,ite_self]
    exact sub_eq_zero.mpr hh.symm
  · have hh:=g.attachLeaves_extensionMatrix_core_leaf hd mate hr q z v k
    simp only [Matrix.sub_apply,normalizedLeafAttachment,vacuumLeafMatrix,
      Matrix.fromBlocks_apply₁₂,vacuumLeafIncidence,Option.some.injEq]
    rw [hh]
    simp only [eq_comm]
    simp
  · have hh:(H.extensionMatrix q z) (.inr l) (.inl w)=
        if w=mate l then treeEdgeWeight d else 0:=by
      simp only [extensionMatrix,boundaryMatrix,spectralMatrix,DeficientGraph.H,normalizedAdjacency,
        boundaryDiagonal,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,
        Matrix.diagonal_apply,Sum.inr_ne_inl,if_false,mul_zero,sub_zero,
        H,attachLeaves,multiLeafGraph,SimpleGraph.adjMatrix_apply]
      by_cases hw:w=mate l <;> simp [hw,treeEdgeWeight,Complex.ofReal_inv]
    simp only [Matrix.sub_apply,normalizedLeafAttachment,vacuumLeafMatrix,
      Matrix.fromBlocks_apply₂₁,Matrix.transpose_apply,vacuumLeafIncidence,Option.some.injEq]
    rw [hh]
    simp only [eq_comm]
    simp
  · have hh:=g.attachLeaves_extensionMatrix_leaf hd mate hr q z l k
    simp only [Matrix.sub_apply,normalizedLeafAttachment,vacuumLeafMatrix,
      Matrix.fromBlocks_apply₂₂,vacuumLeafDiagonal,Option.some_ne_none,if_false]
    rw [hh]
    by_cases hl:l=k
    · subst k
      simp only [Matrix.diagonal_apply_eq,if_true,Sum.elim_inr]
      exact normalized_leaf_residual q z hq0
    · simp [Matrix.diagonal_apply,hl]

end DeficientGraph
end LocalLaw
