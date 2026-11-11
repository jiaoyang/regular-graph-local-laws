import LocalLaw.SourceLocalCommonRows
import LocalLaw.SelectedFirstRegionCharge
import LocalLaw.RestrictedCommonModel

/-! # Fixed true sampled cut rows on every region containing all selected roots -/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1800000
namespace LocalLaw
local instance regionalCommonCutRowsDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace LabelledResamplingState
variable {V:Type} [Fintype V] {T:Set V}{ι:Type}[Fintype ι]

def regionalLostLeafEquiv (s:LabelledResamplingState V T ι)(selector:ℕ)(S:Set (Tᶜ:Set V))
    (hS:s.selectedFirstSet selector⊆S) :
    DeletedLeafIndex ((outsideGraph s.graph T).induce S) (s.partialFirstRemovedSet selector S)≃
      s.OmittedOldLeaves selector S where
  toFun l:=⟨⟨⟨l.1.val.val,l.1.property⟩,l.1.val.property⟩,
    ⟨⟨l.2.val.val.val,l.2.val.property⟩,l.2.property⟩⟩
  invFun l:=⟨⟨⟨l.1.val.val,l.1.property⟩,l.1.val.property⟩,
    ⟨⟨⟨l.2.val.val,hS l.2.val.property⟩,l.2.val.property⟩,l.2.property⟩⟩
  left_inv _:=rfl
  right_inv _:=rfl

def regionalBoundaryMaskEquiv (s:LabelledResamplingState V T ι)(selector:ℕ)(S:Set (Tᶜ:Set V))
    (hA:∀i:s.AdmissibleSampleIndex selector,s.admissibleBoundaryVertex selector i∈S) :
    s.AdmissibleSampleIndex selector≃s.partialBoundaryMask selector S where
  toFun i:=⟨i,hA i⟩
  invFun:=Subtype.val
  left_inv _:=rfl
  right_inv _:=rfl

end LabelledResamplingState
namespace RegularGraph
variable {N d:ℕ}{ι:Type}[Fintype ι]

theorem regional_selected_cut_rows_of_common_rows (g:RegularGraph N d)(T:Set (Fin N))
    (labels:ι≃BoundaryOrientedEdge g.graph T)(samples:LocalSamplingFiber g.graph T)
    (selector:ℕ)(S:Set (Tᶜ:Set (Fin N)))
    (hB:(g.admissibleState T labels samples).selectedFirstSet selector⊆S)
    (hA:∀i:(g.admissibleState T labels samples).AdmissibleSampleIndex selector,
      (g.admissibleState T labels samples).admissibleBoundaryVertex selector i∈S)
    (q z:ℂ)(KM KA:ℝ)
    (hrows:g.LocalCommonIncidenceRows T labels samples selector S q z KM KA) :
    let s:=g.admissibleState T labels samples
    let M:=((g.labelledResampledGraph T labels samples selector).deficient.delete T).restrict S
    let B:=s.partialFirstRemovedSet selector S
    letI:DecidableEq (Bᶜ:Set S):=fun a b=>Classical.propDecidable (a=b)
    ∀u:(Bᶜ:Set S),(∑b:B,‖((M.delete B).extensionGreen q z*M.H.submatrix
      (Subtype.val:(Bᶜ:Set S)→S) (Subtype.val:B→S)) u b‖)≤
      (Real.sqrt ((d:ℝ)-1))⁻¹*(KM+KA) := by
  dsimp only
  let s:=g.admissibleState T labels samples
  let W:=s.selectedFirstSet selector
  let B:=s.partialFirstRemovedSet selector S
  let old:=g.deficient.delete T
  let M:=((g.labelledResampledGraph T labels samples selector).deficient.delete T).restrict S
  let C:=g.omittedCommonModel T labels samples selector S
  let e:=restrictionDeletionGraphIso old.graph S W B (fun _=>Iff.rfl)
  letI:DecidableEq (s.OmittedCore selector S):=fun a b=>Classical.propDecidable (a=b)
  letI:DecidableEq (Bᶜ:Set S):=fun a b=>Classical.propDecidable (a=b)
  have he:((C.extensionGreen q z).submatrix e e)=((old.restrict S).delete B).extensionGreen q z:=by
    exact C.extensionGreen_iso ((old.restrict S).delete B) e
      (old.restrictionDeletion_deficit S W B (fun _=>Iff.rfl) hB) q z
  have hnew:=g.restricted_selectedFirst_deletion_eq T labels samples selector S hB
  change M.delete B=(old.restrict S).delete B at hnew
  have hpoint (u v:(Bᶜ:Set S)):(M.delete B).extensionGreen q z u v=C.extensionGreen q z (e u) (e v):=by
    rw[hnew]
    exact (congrArg (fun P=>P u v) he).symm
  dsimp only[LocalCommonIncidenceRows] at hrows
  intro u
  have hmate:(∑l:DeletedLeafIndex ((outsideGraph s.graph T).induce S) B,
      ‖(M.delete B).extensionGreen q z u l.1‖)≤KM:=by
    let φ:=s.regionalLostLeafEquiv selector S hB
    have hs:=φ.sum_comp (fun l=>‖C.extensionGreen q z (e u) l.1‖)
    have heq:(∑l:DeletedLeafIndex ((outsideGraph s.graph T).induce S) B,
        ‖(M.delete B).extensionGreen q z u l.1‖)=
        ∑l:s.OmittedOldLeaves selector S,‖C.extensionGreen q z (e u) l.1‖:=by
      simp only[hpoint]
      exact hs
    simp only[←finsum_eq_sum_of_fintype] at heq hrows ⊢
    exact heq.le.trans (hrows.1.1 (e u))
  have hbound:(∑i:s.AdmissibleSampleIndex selector,
      ‖(M.delete B).extensionGreen q z u (s.regionalBoundaryCommonVertex selector S hA i)‖)≤KA:=by
    let φ:=s.regionalBoundaryMaskEquiv selector S hA
    have hs:=φ.sum_comp (fun i=>‖C.extensionGreen q z (e u) (s.canonicalBoundaryCoreEmbedding selector S i)‖)
    have heq:(∑i:s.AdmissibleSampleIndex selector,
        ‖(M.delete B).extensionGreen q z u (s.regionalBoundaryCommonVertex selector S hA i)‖)=
        ∑i:s.partialBoundaryMask selector S,‖C.extensionGreen q z (e u) (s.canonicalBoundaryCoreEmbedding selector S i)‖:=by
      simp only[hpoint]
      exact hs
    simp only[←finsum_eq_sum_of_fintype] at heq hrows ⊢
    exact heq.le.trans (hrows.2.1 (e u))
  have hc:=s.selectedFirst_region_new_cut_product_rows d selector S hB hA
    (fun v=>(M.delete B).extensionGreen q z u v)
  change (∑b:B,‖∑v:(Bᶜ:Set S),(M.delete B).extensionGreen q z u v*
    normalizedAdjacency ((outsideGraph (s.fullResample selector).graph T).induce S) d v.val b.val‖)≤_
  simp only[←finsum_eq_sum_of_fintype] at hc hmate hbound ⊢
  exact hc.trans (mul_le_mul_of_nonneg_left (add_le_add hmate hbound)
    (inv_nonneg.mpr (Real.sqrt_nonneg _)))

end RegularGraph
end LocalLaw
