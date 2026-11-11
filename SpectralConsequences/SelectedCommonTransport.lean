import SpectralConsequences.SourceOldMinorCommonComparison
import SpectralConsequences.SwitchedTipCommonComparison

/-! # The ambient T-plus-samples common minor is the literal outside common minor -/
open scoped BigOperators
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance selectedCommonTransportDecidable (p:Prop):Decidable p:=Classical.propDecidable p
variable {V I:Type} {T:Set V}

def retainedBallSampleComplementEquiv (b:I↪(Tᶜ:Set V)) :
    ((Set.range (retainedBallSampleEmbedding T b))ᶜ:Set V) ≃
      ((Set.range b)ᶜ:Set (Tᶜ:Set V)) where
  toFun x:=⟨⟨x.val,fun ht=>x.property ⟨Sum.inr ⟨x.val,ht⟩,rfl⟩⟩,by
    rintro ⟨i,hi⟩
    exact x.property ⟨Sum.inl i,congrArg Subtype.val hi⟩⟩
  invFun x:=⟨x.val.val,by
    rintro ⟨u,hu⟩
    cases u with
    | inl i => exact x.property ⟨i,Subtype.ext hu⟩
    | inr t => exact x.val.property (hu ▸ t.property)⟩
  left_inv _:=rfl
  right_inv _:=rfl

variable [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

omit [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I] in
theorem sample_own_ambient_mem_iff (b:I↪(Tᶜ:Set V)) (Q:Set I) (v:V) :
    v∈(retainedBallSampleEmbedding T b) '' sampleOwnRetainedSet T Q ↔
      ∃i∈Q,(b i).val=v := by
  constructor
  · rintro ⟨u,⟨i,hi,rfl⟩,hu⟩
    exact ⟨i,hi,hu⟩
  · rintro ⟨i,hi,hu⟩
    exact ⟨Sum.inl i,⟨i,hi,rfl⟩,hu⟩

theorem oldCommonSampleEntry_eq_outside_common {N d:ℕ} {ι:Type} [Fintype ι]
    (g:RegularGraph N d) (T:Set (Fin N))
    (labels:ι≃BoundaryOrientedEdge g.graph T) (samples:LocalSamplingFiber g.graph T)
    (selector:ℕ) (z:ℂ)
    (i j:(g.admissibleState T labels samples).AdmissibleSampleIndex selector) :
    let s:=g.admissibleState T labels samples
    oldCommonSampleEntry g.H T (s.selectedFirstEmbedding selector) (s.admissibleSecondVertex selector)
      (selected_first_ne_second s selector) z i j =
      ((g.deficient.delete T).delete (s.selectedFirstSet selector)).G z
        (selectedTipOutsideFirsts s selector i) (selectedTipOutsideFirsts s selector j) := by
  dsimp only
  let s:=g.admissibleState T labels samples
  let b:=s.selectedFirstEmbedding selector
  let e:=retainedBallSampleComplementEquiv b
  let common:=(g.deficient.delete T).delete (s.selectedFirstSet selector)
  have hM : (g.H.submatrix
      (Subtype.val:((Set.range (retainedBallSampleEmbedding T b))ᶜ:Set (Fin N))→Fin N)
      (Subtype.val:((Set.range (retainedBallSampleEmbedding T b))ᶜ:Set (Fin N))→Fin N))=
        common.H.submatrix e e := by
    rw [DeficientGraph.H_delete,DeficientGraph.H_delete]
    ext u v
    rfl
  dsimp only [oldCommonSampleEntry]
  rw [hM]
  have hg := green_reindex_equiv common.H e z
  have hh := congrArg (fun M => M
    (sampleTipRetainedComplement T b (s.admissibleSecondVertex selector) (selected_first_ne_second s selector) i)
    (sampleTipRetainedComplement T b (s.admissibleSecondVertex selector) (selected_first_ne_second s selector) j)) hg
  exact hh

end SpectralConsequences
