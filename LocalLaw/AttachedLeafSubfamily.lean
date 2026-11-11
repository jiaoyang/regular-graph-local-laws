import LocalLaw.NormalizedLeafPrecision
import LocalLaw.LeafSchurModel

/-! # Literal principal deletion of an arbitrary subfamily of attached leaves

Keeping all core vertices and an injectively indexed leaf subfamily yields
the actual model attached with just that subfamily. The changed core deficit
is exactly offset by its changed degree, so the core precision is unchanged.
-/

noncomputable section
namespace LocalLaw
local instance attachedLeafSubfamilyDecidable (p:Prop):Decidable p:=Classical.propDecidable p
variable {V L J:Type}[Fintype V][Fintype L][Fintype J]

omit [Fintype V] [Fintype J] in
theorem subfamily_leaf_multiplicity_le (mate:L→V)(e:J↪L)(v:V) :
    multiLeafMultiplicity (mate∘e) v ≤ multiLeafMultiplicity mate v := by
  apply Nat.card_le_card_of_injective
    (fun j:{j:J //(mate∘e) j=v}=>(⟨e j.val,j.property⟩:{l:L //mate l=v}))
  intro i j h
  exact Subtype.ext (e.injective (congrArg Subtype.val h))

namespace DeficientGraph
variable {d:ℕ}

theorem attachLeaves_subfamily_extensionMatrix (g:DeficientGraph V d)(hd:3≤d)(mate:L→V)
    (hrestore:∀v,multiLeafMultiplicity mate v≤g.deficit v)(e:J↪L)(q z:ℂ) :
    let hsub:∀v,multiLeafMultiplicity (mate∘e) v≤g.deficit v:=
      fun v=>(subfamily_leaf_multiplicity_le mate e v).trans (hrestore v)
    ((g.attachLeaves (by omega) mate hrestore).extensionMatrix q z).submatrix
      (Sum.map id e) (Sum.map id e)=(g.attachLeaves (by omega) (mate∘e) hsub).extensionMatrix q z := by
  dsimp only
  let hs:∀v,multiLeafMultiplicity (mate∘e) v≤g.deficit v:=
    fun v=>(subfamily_leaf_multiplicity_le mate e v).trans (hrestore v)
  ext i j
  cases i with
  | inl i=>
    cases j with
    | inl j=>
      have ha:=congrArg (fun M:Matrix V V ℂ=>M i j)
        (g.attachLeaves_extensionMatrix_principal (by omega) mate hrestore q z)
      have hb:=congrArg (fun M:Matrix V V ℂ=>M i j)
        (g.attachLeaves_extensionMatrix_principal (by omega) (mate∘e) hs q z)
      exact ha.trans hb.symm
    | inr j=>
      simp only [extensionMatrix,boundaryMatrix,spectralMatrix,H,boundaryDiagonal,
        Matrix.submatrix_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
        Matrix.one_apply,Matrix.diagonal_apply,Sum.inl_ne_inr,if_false,mul_zero,sub_zero,
        normalizedAdjacency,SimpleGraph.adjMatrix_apply,attachLeaves,multiLeafGraph,
        Sum.map_inl,Sum.map_inr,id_eq,Function.comp_apply]
  | inr i=>
    cases j with
    | inl j=>
      simp only [extensionMatrix,boundaryMatrix,spectralMatrix,H,boundaryDiagonal,
        Matrix.submatrix_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
        Matrix.one_apply,Matrix.diagonal_apply,Sum.inr_ne_inl,if_false,mul_zero,sub_zero,
        normalizedAdjacency,SimpleGraph.adjMatrix_apply,attachLeaves,multiLeafGraph,
        Sum.map_inl,Sum.map_inr,id_eq,Function.comp_apply]
    | inr j=>
      have ha:=congrArg (fun M:Matrix J J ℂ=>M i j)
        (g.attachLeaves_leaf_precision_block hd mate hrestore e q z)
      have hb:=congrArg (fun M:Matrix J J ℂ=>M i j)
        (g.attachLeaves_leaf_precision_block hd (mate∘e) hs (Function.Embedding.refl J) q z)
      exact ha.trans hb.symm

theorem attachLeaves_subfamily_extensionGreen (g:DeficientGraph V d)(hd:3≤d)(mate:L→V)
    (hrestore:∀v,multiLeafMultiplicity mate v≤g.deficit v)(e:J↪L)(q z:ℂ) :
    let hsub:∀v,multiLeafMultiplicity (mate∘e) v≤g.deficit v:=
      fun v=>(subfamily_leaf_multiplicity_le mate e v).trans (hrestore v)
    (g.attachLeaves (by omega) (mate∘e) hsub).extensionGreen q z=
      (((g.attachLeaves (by omega) mate hrestore).extensionMatrix q z).submatrix
        (Sum.map id e) (Sum.map id e))⁻¹ := by
  dsimp only
  rw [g.attachLeaves_subfamily_extensionMatrix hd mate hrestore e q z]
  rfl

end DeficientGraph
end LocalLaw
