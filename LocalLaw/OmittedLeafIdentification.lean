import LocalLaw.OmittedLeafModels
import LocalLaw.NormalizedLeafAttachment

/-! # Exact actual new-core identification after normalized kept-slot Schur

The complete kept-slot multiplicity is the literal omitted-neighbor charge.
Lowering that many common deficits gives the actual new local model after
retained B vertices are deleted. The normalized completed matrix is proved
nonsingular and its core inverse is this same actual new Green function.
-/

noncomputable section
set_option maxHeartbeats 3000000
namespace LocalLaw
local instance omittedLeafIdentificationDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace RegularGraph
variable {N d:ℕ}{ι:Type}[Fintype ι]

def omittedKeptRestoredModel (g:RegularGraph N d)(T:Set (Fin N))
    (labels:ι≃BoundaryOrientedEdge g.graph T)(samples:LocalSamplingFiber g.graph T)
    (selector:ℕ)(S:Set (Tᶜ:Set (Fin N))) :=
  (g.omittedCommonModel T labels samples selector S).lowerDeficit
    (multiLeafMultiplicity ((g.admissibleState T labels samples).omittedAllMate selector S ∘
      (g.admissibleState T labels samples).omittedKeptEmbedding selector S))
    (g.omittedKeptMate_restore_budget T labels samples selector S)

theorem omittedKeptRestoredModel_extensionMatrix (g:RegularGraph N d)(T:Set (Fin N))
    (labels:ι≃BoundaryOrientedEdge g.graph T)(samples:LocalSamplingFiber g.graph T)
    (selector:ℕ)(S:Set (Tᶜ:Set (Fin N)))(q z:ℂ) :
    let s:=g.admissibleState T labels samples
    let W:=s.selectedFirstSet selector
    let B:=s.partialFirstRemovedSet selector S
    let new:=(g.labelledResampledGraph T labels samples selector).deficient.delete T
    let e:=restrictionDeletionGraphIso new.graph S W B (fun _=>Iff.rfl)
    ((g.omittedKeptRestoredModel T labels samples selector S).extensionMatrix q z).submatrix e e=
      ((new.restrict S).delete B).extensionMatrix q z := by
  dsimp only
  let s:=g.admissibleState T labels samples
  let W:=s.selectedFirstSet selector
  let B:=s.partialFirstRemovedSet selector S
  let C:=g.omittedCommonModel T labels samples selector S
  let new:=(g.labelledResampledGraph T labels samples selector).deficient.delete T
  let e:=restrictionDeletionGraphIso new.graph S W B (fun _=>Iff.rfl)
  let ρ:=multiLeafMultiplicity (s.omittedAllMate selector S ∘s.omittedKeptEmbedding selector S)
  have hL:=C.lowerDeficit_extensionMatrix ρ
    (g.omittedKeptMate_restore_budget T labels samples selector S) q z
  have hP:=g.actual_omitted_switching_precision T labels samples selector S q z
  change ((C.lowerDeficit ρ (g.omittedKeptMate_restore_budget T labels samples selector S)).extensionMatrix q z).submatrix e e=
    ((new.restrict S).delete B).extensionMatrix q z
  ext i j
  have hLi:=congrArg (fun A:Matrix (s.OmittedCore selector S) (s.OmittedCore selector S) ℂ=>A (e i) (e j)) hL
  have hPi:=congrArg (fun A:Matrix (Bᶜ:Set S) (Bᶜ:Set S) ℂ=>A i j) hP
  simp only [Matrix.submatrix_apply,Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.diagonal_apply] at hLi hPi ⊢
  by_cases hij:i=j
  · subst j
    simp only [if_pos rfl] at hLi hPi
    have hρ:ρ (e i)=Nat.card (s.OmittedOrdinarySlot selector S i.val.val)+
        Nat.card (s.OmittedAddedSlot selector S i.val.val):=s.omittedKeptMultiplicity selector S (e i)
    have hs:(((ρ (e i):ℝ)/((d:ℝ)-1)):ℂ)=
        (Nat.card (s.OmittedOrdinarySlot selector S i.val.val)+
          Nat.card (s.OmittedAddedSlot selector S i.val.val):ℂ)/((d:ℂ)-1):=by
      rw [hρ]
      push_cast
      rfl
    rw [hs] at hLi
    linear_combination hLi+hPi
  · have heij:e i≠e j:=fun h=>hij (e.injective h)
    simp only [if_neg hij,if_neg heij,mul_zero,sub_zero,add_zero] at hLi hPi
    exact hLi.trans hPi

theorem omittedKeptRestoredModel_extensionGreen (g:RegularGraph N d)(T:Set (Fin N))
    (labels:ι≃BoundaryOrientedEdge g.graph T)(samples:LocalSamplingFiber g.graph T)
    (selector:ℕ)(S:Set (Tᶜ:Set (Fin N)))(q z:ℂ) :
    let s:=g.admissibleState T labels samples
    let W:=s.selectedFirstSet selector
    let B:=s.partialFirstRemovedSet selector S
    let new:=(g.labelledResampledGraph T labels samples selector).deficient.delete T
    let e:=restrictionDeletionGraphIso new.graph S W B (fun _=>Iff.rfl)
    ((g.omittedKeptRestoredModel T labels samples selector S).extensionGreen q z).submatrix e e=
      ((new.restrict S).delete B).extensionGreen q z := by
  dsimp only
  let s:=g.admissibleState T labels samples
  let W:=s.selectedFirstSet selector
  let B:=s.partialFirstRemovedSet selector S
  let new:=(g.labelledResampledGraph T labels samples selector).deficient.delete T
  let e:=restrictionDeletionGraphIso new.graph S W B (fun _=>Iff.rfl)
  let C:=g.omittedKeptRestoredModel T labels samples selector S
  have hh:=Matrix.inv_submatrix_equiv (C.extensionMatrix q z) e.toEquiv e.toEquiv
  change ((C.extensionMatrix q z).submatrix e e)⁻¹=
    (C.extensionMatrix q z)⁻¹.submatrix e e at hh
  rw [g.omittedKeptRestoredModel_extensionMatrix T labels samples selector S q z] at hh
  exact hh.symm

end RegularGraph
end LocalLaw
