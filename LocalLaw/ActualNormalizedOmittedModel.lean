import LocalLaw.OmittedLeafIdentification
import LocalLaw.OmittedLeafBudget
import LocalLaw.AttachedLeafSubfamily

/-! # Genuine normalized omitted-slot model for the actual switched minor

The matrix is proved nonsingular from the actual deficient common model.
Its core inverse, after the literal vertex reindexing, is exactly the new
partially deleted reference Green function. The all-to-kept principal
matrix relation also retains the actual inherited deficit convention.
-/

noncomputable section
set_option maxHeartbeats 3000000
namespace LocalLaw
local instance actualNormalizedOmittedDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace RegularGraph
variable {N d:ℕ}{ι:Type}[Fintype ι]

theorem actual_normalized_omitted_unit_core (g:RegularGraph N d)(hd:3≤d)(T:Set (Fin N))
    (labels:ι≃BoundaryOrientedEdge g.graph T)(samples:LocalSamplingFiber g.graph T)
    (selector:ℕ)(S:Set (Tᶜ:Set (Fin N)))(q z:ℂ)(hq0:q≠0)(hz:0<z.im)(hq:0≤q.im) :
    let s:=g.admissibleState T labels samples
    let C:=g.omittedCommonModel T labels samples selector S
    let mate:=s.omittedAllMate selector S ∘s.omittedKeptEmbedding selector S
    letI:DecidableEq (s.OmittedCore selector S):=fun a b=>Classical.propDecidable (a=b)
    letI:DecidableEq (s.OmittedOrdinaryLeaves selector S⊕s.OmittedExtraLeaves selector S):=
      fun a b=>Classical.propDecidable (a=b)
    IsUnit (C.normalizedLeafAttachment mate q z) ∧
      ((C.normalizedLeafAttachment mate q z)⁻¹).toBlocks₁₁=
        (g.omittedKeptRestoredModel T labels samples selector S).extensionGreen q z := by
  dsimp only
  exact (g.omittedCommonModel T labels samples selector S).normalizedLeafAttachment_unit_core hd _
    (g.omittedKeptMate_restore_budget T labels samples selector S) q z hq0 hz hq

theorem actual_omitted_all_to_kept_precision (g:RegularGraph N d)(hd:3≤d)(T:Set (Fin N))
    (labels:ι≃BoundaryOrientedEdge g.graph T)(samples:LocalSamplingFiber g.graph T)
    (selector:ℕ)(S:Set (Tᶜ:Set (Fin N)))(q z:ℂ) :
    let s:=g.admissibleState T labels samples
    let C:=g.omittedCommonModel T labels samples selector S
    let all:=s.omittedAllMate selector S
    let e:=s.omittedKeptEmbedding selector S
    ((g.omittedAllCompletion (by omega) T labels samples selector S).extensionMatrix q z).submatrix
      (Sum.map id e) (Sum.map id e)=
        (C.attachLeaves (by omega) (all∘e) (g.omittedKeptMate_restore_budget T labels samples selector S)).extensionMatrix q z := by
  dsimp only
  have hh:=(g.omittedCommonModel T labels samples selector S).attachLeaves_subfamily_extensionMatrix hd
    ((g.admissibleState T labels samples).omittedAllMate selector S)
    (g.omittedAllMate_restore_budget T labels samples selector S)
    ((g.admissibleState T labels samples).omittedKeptEmbedding selector S) q z
  ext i j
  have he:=congrArg (fun M=>M i j) hh
  by_cases hij:i=j
  · subst j
    simpa only [DeficientGraph.extensionMatrix,boundaryMatrix,spectralMatrix,
      DeficientGraph.boundaryDiagonal,Matrix.submatrix_apply,Matrix.sub_apply,Matrix.smul_apply,
      smul_eq_mul,Matrix.one_apply,Matrix.diagonal_apply,if_pos rfl] using he
  · have hf:Function.Injective (Sum.map (id (α:=(g.admissibleState T labels samples).OmittedCore selector S)) ((g.admissibleState T labels samples).omittedKeptEmbedding selector S)):=
      Function.Injective.sumMap (f:=id (α:=(g.admissibleState T labels samples).OmittedCore selector S)) Function.injective_id
        ((g.admissibleState T labels samples).omittedKeptEmbedding selector S).injective
    have himg:(Sum.map id ((g.admissibleState T labels samples).omittedKeptEmbedding selector S)) i≠
      (Sum.map id ((g.admissibleState T labels samples).omittedKeptEmbedding selector S)) j:=fun h=>hij (hf h)
    simpa only [DeficientGraph.extensionMatrix,boundaryMatrix,spectralMatrix,
      DeficientGraph.boundaryDiagonal,Matrix.submatrix_apply,Matrix.sub_apply,Matrix.smul_apply,
      smul_eq_mul,Matrix.one_apply,Matrix.diagonal_apply,if_neg hij,if_neg himg] using he

end RegularGraph
end LocalLaw
