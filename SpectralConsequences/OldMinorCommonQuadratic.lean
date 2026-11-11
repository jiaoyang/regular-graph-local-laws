import SpectralConsequences.NestedCommonComparison
import SpectralConsequences.RetainedBallSampleInverse
import SpectralConsequences.IndexedCrossDeletion
import LocalLaw.NearDiagonalInverse

/-! # A small own-sample minor compared with the common T-plus-samples minor

All matrices are actual Hermitian resolvents. Only diagonal reciprocal,
separated cross-entry, and retained-precision row bounds enter; the common
comparison is proved by two exact Schur identities.
-/
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1600000
namespace SpectralConsequences
open LocalLaw
local instance oldMinorCommonQuadraticDecidable (p:Prop):Decidable p:=Classical.propDecidable p
variable {V I:Type} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

def sampleOwnRetainedSet (T:Set V) (Q:Set I) : Set (I⊕T) := (Sum.inl:I→I⊕T) '' Q

def sampleTipRetainedComplement (T:Set V) (b:I↪(Tᶜ:Set V)) (c:I→(Tᶜ:Set V))
    (hcb:∀i j,b j≠c i) (i:I) : ((Set.range (retainedBallSampleEmbedding T b))ᶜ:Set V) :=
  ⟨(c i).val,by
    rintro ⟨u,hu⟩
    cases u with
    | inl j => exact hcb i j (Subtype.ext hu)
    | inr t => exact (c i).property (hu ▸ t.property)⟩

def sampleOwnEquiv (T:Set V) (b:I↪(Tᶜ:Set V)) (Q:Set I) :
    Q ≃ ((retainedBallSampleEmbedding T b) '' sampleOwnRetainedSet T Q) :=
  Equiv.ofBijective
    (fun i=>⟨(b i.val).val,⟨Sum.inl i.val,⟨i.val,i.property,rfl⟩,rfl⟩⟩)
    (by
      constructor
      · intro i j hij
        have heq : (b i.val).val=(b j.val).val := congrArg (fun x => x.val) hij
        exact Subtype.ext (b.injective (Subtype.ext heq))
      · rintro ⟨v,u,⟨i,hi,rfl⟩,hv⟩
        exact ⟨⟨i,hi⟩,Subtype.ext hv⟩)

theorem old_small_minor_common_quadratic (H:Matrix V V ℂ) (hH:H.IsHermitian)
    (T:Set V) (b:I↪(Tᶜ:Set V)) (c:I→(Tᶜ:Set V)) (hcb:∀i j,b j≠c i)
    (z:ℂ) (hz:0<z.im) (P A C ε:ℝ) (hP:0≤P) (hA:0≤A) (hC:0≤C) (hε:0≤ε)
    (hrows:∀i,∑j,‖((green H z).submatrix (retainedBallSampleEmbedding T b)
      (retainedBallSampleEmbedding T b))⁻¹ i j‖≤C)
    (hpivot:∀i,‖(green H z (b i).val (b i).val)⁻¹‖≤P)
    (hbb:∀i j,i≠j→‖green H z (b i).val (b j).val‖≤ε)
    (hcbfar:∀i j,i≠j→‖green H z (c i).val (b j).val‖≤ε)
    (hbcfar:∀i j,i≠j→‖green H z (b j).val (c i).val‖≤ε)
    (hcbown:∀i,‖green H z (c i).val (b i).val‖≤A)
    (hbcown:∀i,‖green H z (b i).val (c i).val‖≤A)
    (hbt:∀i (t:T),‖green H z (b i).val t.val‖≤ε)
    (htb:∀i (t:T),‖green H z t.val (b i).val‖≤ε)
    (hct:∀i (t:T),‖green H z (c i).val t.val‖≤ε)
    (htc:∀i (t:T),‖green H z t.val (c i).val‖≤ε)
    (hεA:ε≤A) (Q:Set I) (hcard:Nat.card Q≤2)
    (hsmall:(Fintype.card Q:ℝ)*P*ε≤1/2)
    (i j:I) (hi:i∈Q) (hj:j∈Q) :
    let f:=retainedBallSampleEmbedding T b
    let O:=f '' sampleOwnRetainedSet T Q
    let x:=sampleTipRetainedComplement T b c hcb i
    let y:=sampleTipRetainedComplement T b c hcb j
    let xo:(Oᶜ:Set V):=⟨x.val,fun h=>x.property (by obtain ⟨u,_,hu⟩:=h;exact ⟨u,hu⟩)⟩
    let yo:(Oᶜ:Set V):=⟨y.val,fun h=>y.property (by obtain ⟨u,_,hu⟩:=h;exact ⟨u,hu⟩)⟩
    ‖green (H.submatrix (Subtype.val:(Oᶜ:Set V)→V) (Subtype.val:(Oᶜ:Set V)→V)) z xo yo-
      green (H.submatrix (Subtype.val:((Set.range f)ᶜ:Set V)→V)
        (Subtype.val:((Set.range f)ᶜ:Set V)→V)) z x y‖≤
      (Fintype.card (I⊕T):ℝ)*C*((1+4*P*A)*ε)^2 := by
  dsimp only
  let f:=retainedBallSampleEmbedding T b
  let RQ:=sampleOwnRetainedSet T Q
  let O:Set V:=f '' RQ
  let φ:Q≃O:=sampleOwnEquiv T b Q
  let x:=sampleTipRetainedComplement T b c hcb i
  let y:=sampleTipRetainedComplement T b c hcb j
  let K:=H.submatrix (Subtype.val:(Oᶜ:Set V)→V) (Subtype.val:(Oᶜ:Set V)→V)
  let own:Matrix Q Q ℂ:=(green H z).submatrix (fun k=>(b k.val).val) (fun k=>(b k.val).val)
  have hown:IsUnit own:=embedded_green_submatrix_isUnit H hH z hz
    ⟨fun k:Q=>(b k.val).val,fun k l h=>Subtype.ext (b.injective (Subtype.ext h))⟩
  have hownrows:∀k,∑l,‖own⁻¹ k l‖≤2*P:=by
    apply inverse_rows_of_small_offdiagonal own hown P ((Fintype.card Q:ℝ)*ε) hP (by positivity)
    · intro k
      exact green_diagonal_ne_zero H hH z hz (b k.val).val
    · intro k
      exact hpivot k.val
    · intro k
      calc
        _ ≤ ∑_l:Q,ε:=by
          apply Finset.sum_le_sum
          intro l _
          by_cases hkl:k=l
          · subst l
            simpa only [Matrix.sub_apply,Matrix.diagonal_apply_eq,sub_self,norm_zero] using hε
          · have hne:k.val≠l.val:=fun h=>hkl (Subtype.ext h)
            simpa only [Matrix.sub_apply,Matrix.diagonal_apply_ne _ hkl,sub_zero] using hbb k.val l.val hne
        _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    · nlinarith only [hsmall]
  have hn:(Fintype.card Q:ℝ)≤2:=by simpa only [Nat.card_eq_fintype_card] using (Nat.cast_le (α:=ℝ).mpr hcard)
  have hφm : (green H z).submatrix (fun u:Q=>(φ u).val) (fun u:Q=>(φ u).val)=own := by
    ext u v
    rfl
  have hφrows : ∀k,∑l,‖((green H z).submatrix (fun u:Q=>(φ u).val)
      (fun u:Q=>(φ u).val))⁻¹ k l‖≤2*P := by
    rw [hφm]
    exact hownrows
  have hbound:∀k∈Q,∀v:(RQᶜ:Set (I⊕T)),
      ‖green K z
        ⟨(c k).val,fun h=>(sampleTipRetainedComplement T b c hcb k).property (by obtain ⟨u,_,hu⟩:=h;exact ⟨u,hu⟩)⟩
        (embeddingOutsideImage f RQ v)‖≤(1+4*P*A)*ε := by
    intro k hk v
    have hraw:‖green H z (c k).val (f v.val)‖≤ε:=by
      rcases v with ⟨v,hv⟩
      cases v with
      | inl l =>
        have hkl:k≠l:=by rintro rfl;exact hv ⟨k,hk,rfl⟩
        exact hcbfar k l hkl
      | inr t => exact hct k t
    have hleft:∀u:Q,‖green H z (c k).val (φ u).val‖≤A:=by
      intro u
      by_cases hku:k=u.val
      · subst k
        exact hcbown u.val
      · exact (hcbfar k u.val hku).trans hεA
    have hright:∀u:Q,‖green H z (φ u).val (f v.val)‖≤ε:=by
      intro u
      rcases v with ⟨v,hv⟩
      cases v with
      | inl l =>
        have hul:u.val≠l:=by intro h; subst l;exact hv ⟨u.val,u.property,rfl⟩
        exact hbb u.val l hul
      | inr t => exact hbt u.val t
    let xx : (Oᶜ:Set V) := ⟨(c k).val,fun h =>
      (sampleTipRetainedComplement T b c hcb k).property (by obtain ⟨u,_,hu⟩:=h;exact ⟨u,hu⟩)⟩
    have hh:=physical_indexed_deleted_entry_bound H hH O φ z hz (2*P) A ε ε
      (by positivity) hA hε hφrows xx (embeddingOutsideImage f RQ v) hraw hleft hright
    have hmass:=mul_le_mul_of_nonneg_right hn (show 0≤(2*P)*A*ε by positivity)
    exact hh.trans (by nlinarith only [hmass])
  have hboundR:∀k∈Q,∀v:(RQᶜ:Set (I⊕T)),
      ‖green K z (embeddingOutsideImage f RQ v)
        ⟨(c k).val,fun h=>(sampleTipRetainedComplement T b c hcb k).property (by obtain ⟨u,_,hu⟩:=h;exact ⟨u,hu⟩)⟩‖≤(1+4*P*A)*ε := by
    intro k hk v
    have hraw:‖green H z (f v.val) (c k).val‖≤ε:=by
      rcases v with ⟨v,hv⟩
      cases v with
      | inl l =>
        have hkl:k≠l:=by rintro rfl;exact hv ⟨k,hk,rfl⟩
        exact hbcfar k l hkl
      | inr t => exact htc k t
    have hleft:∀u:Q,‖green H z (f v.val) (φ u).val‖≤ε:=by
      intro u
      rcases v with ⟨v,hv⟩
      cases v with
      | inl l =>
        have hlu:l≠u.val:=by intro h; subst l;exact hv ⟨u.val,u.property,rfl⟩
        exact hbb l u.val hlu
      | inr t => exact htb u.val t
    have hright:∀u:Q,‖green H z (φ u).val (c k).val‖≤A:=by
      intro u
      by_cases hku:k=u.val
      · subst k
        exact hbcown u.val
      · exact (hbcfar k u.val hku).trans hεA
    let yy : (Oᶜ:Set V) := ⟨(c k).val,fun h =>
      (sampleTipRetainedComplement T b c hcb k).property (by obtain ⟨u,_,hu⟩:=h;exact ⟨u,hu⟩)⟩
    have hh:=physical_indexed_deleted_entry_bound H hH O φ z hz (2*P) ε A ε
      (by positivity) hε hA hφrows (embeddingOutsideImage f RQ v) yy hraw hleft hright
    have hmass:=mul_le_mul_of_nonneg_right hn (show 0≤(2*P)*ε*A by positivity)
    exact hh.trans (by nlinarith only [hmass])
  exact retained_nested_common_quadratic H hH z hz f RQ C ((1+4*P*A)*ε) hC (by positivity)
    hrows x y (hbound i hi) (hboundR j hj)

end SpectralConsequences
