import LocalLaw.MultiLeafAugmentation
import LocalLaw.VacuumLeafSchur

/-! # The actual pendant-leaf precision and its exact q normalization error

With Ext=H-zI-qD, the leaf diagonal is -z-q. Replacing it by q^-1
changes it by (1+z*q+q^2)/q. Thus the normalized Schur self-energy has
the same sign as the exact missing-neighbor boundary charge.
-/

noncomputable section
namespace LocalLaw
local instance normalizedLeafPrecisionDecidable (p:Prop):Decidable p:=Classical.propDecidable p

theorem normalized_leaf_residual (q z:ℂ)(hq:q≠0) :
    q⁻¹-(-z-q)=(1+z*q+q^2)/q := by
  field_simp
  ring

namespace DeficientGraph
variable {V L J:Type*}[Fintype V][Fintype L]{d:ℕ}

theorem attachLeaves_boundaryCoefficient_leaf (g:DeficientGraph V d)(hd:3≤d)(mate:L→V)
    (hrestore:∀v,multiLeafMultiplicity mate v≤g.deficit v)(l:L) :
    (g.attachLeaves (by omega) mate hrestore).boundaryCoefficient (.inr l)=1 := by
  have hdeg:=multiLeafGraph_degree_leaf g.graph mate l
  have hdR:(3:ℝ)≤d:=Nat.cast_le.mpr hd
  unfold boundaryCoefficient
  simp only [attachLeaves,Sum.elim_inr,Nat.cast_zero,sub_zero]
  simp only [←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] at hdeg ⊢
  rw [hdeg]
  simp only [Nat.cast_one]
  exact div_self (by linarith)

/-- Any injectively selected retained leaf block has the actual scalar
precision (-z-q)I. This includes arbitrary partial leaf masks. -/
theorem attachLeaves_leaf_precision_block (g:DeficientGraph V d)(hd:3≤d)(mate:L→V)
    (hrestore:∀v,multiLeafMultiplicity mate v≤g.deficit v)(e:J↪L)(q z:ℂ) :
    ((g.attachLeaves (by omega) mate hrestore).extensionMatrix q z).submatrix
      (fun j=>Sum.inr (e j)) (fun j=>Sum.inr (e j))=(-z-q)•(1:Matrix J J ℂ) := by
  ext i j
  simp only [extensionMatrix,boundaryMatrix,spectralMatrix,H,boundaryDiagonal,
    Matrix.submatrix_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.one_apply,Matrix.diagonal_apply,Sum.inr.injEq,e.injective.eq_iff]
  rw [g.attachLeaves_boundaryCoefficient_leaf hd mate hrestore]
  simp only [normalizedAdjacency,Matrix.smul_apply,smul_eq_mul,SimpleGraph.adjMatrix_apply,
    attachLeaves,multiLeafGraph,if_false,mul_zero]
  by_cases hij:i=j <;> simp [hij]

theorem attachLeaves_leaf_normalization_error (g:DeficientGraph V d)(hd:3≤d)(mate:L→V)
    (hrestore:∀v,multiLeafMultiplicity mate v≤g.deficit v)(e:J↪L)(q z:ℂ)(hq:q≠0) :
    q⁻¹•(1:Matrix J J ℂ)-
      ((g.attachLeaves (by omega) mate hrestore).extensionMatrix q z).submatrix
        (fun j=>Sum.inr (e j)) (fun j=>Sum.inr (e j))=
      ((1+z*q+q^2)/q)•1 := by
  rw [g.attachLeaves_leaf_precision_block hd mate hrestore e q z,←sub_smul,normalized_leaf_residual q z hq]

end DeficientGraph
end LocalLaw
