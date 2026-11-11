import LocalLaw.NormalizedLeafAttachment
import LocalLaw.SupportedSmallUpdate

/-! # Quantitative replacement of actual leaves by q-normalized leaves

The normalized core is the literal deficit-restored model. All matrix and
retained-block units, symmetry and perturbation masses are derived; the
only analytic inputs are actual old leaf and target L1 bounds and the
finite contraction condition.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1800000
namespace LocalLaw
local instance normalizedLeafTargetDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace DeficientGraph
variable {V I:Type} [Fintype V] [Fintype I] {d:ℕ}

theorem normalized_leaf_target_stability (g:DeficientGraph V d)(hd:3≤d)
    (mate:I→V)(hr:∀v,multiLeafMultiplicity mate v≤g.deficit v)
    (q z:ℂ)(hq0:q≠0)(hz:0<z.im)(hq:0≤q.im)(C a b:ℝ)
    (hC:0≤C)(ha:0≤a)(hb:0≤b) :
    let H:=g.attachLeaves (by omega) mate hr
    let G:=H.extensionGreen q z
    let δ:=‖(1+z*q+q^2)/q‖
    (∀l,∑k:I,‖G (.inr l) (.inr k)‖≤C)→
    (Fintype.card I:ℝ)*C*δ≤1/2→
    ∀x y:V,(∑l:I,‖G (.inl x) (.inr l)‖)≤a→
      (∑l:I,‖G (.inl y) (.inr l)‖)≤b→
    ‖G (.inl x) (.inl y)-(g.lowerDeficit (multiLeafMultiplicity mate) hr).extensionGreen q z x y‖≤
      a*δ*(b*(1+δ*(2*C))) := by
  dsimp only
  let H:=g.attachLeaves (by omega) mate hr
  let A:=H.extensionMatrix q z
  let B:=g.normalizedLeafAttachment mate q z
  let res:=(1+z*q+q^2)/q
  let δ:=‖res‖
  let f:V⊕I→ℂ:=Sum.elim (fun _=>0) (fun _=>res)
  let e:I↪V⊕I:=⟨Sum.inr,Sum.inr_injective⟩
  have hA:IsUnit A:=H.extensionMatrix_isUnit hd q z hz hq
  have hN:=g.normalizedLeafAttachment_unit_core hd mate hr q z hq0 hz hq
  have hB:IsUnit B:=hN.1
  have hdiff:B-A=Matrix.diagonal f:=g.normalizedLeafAttachment_difference hd mate hr q z hq0
  have hs:∀x y,x∉Set.range e∨y∉Set.range e→(B-A) x y=0:=by
    intro x y hxy
    rw [hdiff,Matrix.diagonal_apply]
    by_cases he:x=y
    · subst y
      rcases x with v|l
      · simp [f]
      · have hm:(.inr l:V⊕I)∈Set.range e:=⟨l,rfl⟩
        exact False.elim (hxy.elim (fun h=>h hm) (fun h=>h hm))
    · simp [he]
  have he:∀l k,‖(B-A) (e l) (e k)‖≤δ:=by
    intro l k
    rw [hdiff]
    by_cases hl:l=k
    · subst k
      simp only [Matrix.diagonal_apply_eq,e,f,Function.Embedding.coeFn_mk,Sum.elim_inr]
      exact le_rfl
    · simp [Matrix.diagonal_apply,e,hl,f,δ]
  have hW:∀l,∑k:I,‖(B-A) (e l) (e k)‖≤δ:=by
    intro l
    rw [hdiff]
    simp [Matrix.diagonal_apply,e,f,apply_ite norm,δ]
  have hP:IsUnit (A⁻¹.submatrix e e):=(g.attachLeaves_Green_leaf_schur hd mate hr q z hz hq).1
  have hAi:A⁻¹.IsSymm:=H.extensionGreen_isSymm q z
  have hAii:A⁻¹⁻¹=A:=Matrix.nonsing_inv_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hA)
  have hAs:A.transpose=A:=by
    have hh:=congrArg (fun M:Matrix (V⊕I) (V⊕I) ℂ=>M⁻¹) hAi
    dsimp only at hh
    rw [←Matrix.transpose_nonsing_inv A⁻¹,hAii] at hh
    exact hh
  have hNform:B=A+Matrix.diagonal f:=by rw [←hdiff];abel
  have hBs:B.transpose=B:=by
    rw [hNform,Matrix.transpose_add,Matrix.diagonal_transpose,hAs]
  have hBis:B⁻¹.IsSymm:=by
    change B⁻¹.transpose=B⁻¹
    rw [Matrix.transpose_nonsing_inv,hBs]
  intro hrows hsmall x y hx hy
  have hcols:∀k,∑l:I,‖A⁻¹ (e l) (e k)‖≤C:=by
    intro k
    simpa only [hAi.apply] using hrows k
  have hh:=supported_small_update_target A B hA hB e hs hP C δ δ a b hC (norm_nonneg _)
    (norm_nonneg _) ha hb hrows hcols he hsmall hW hBis (.inl x) (.inl y) hx hy
  have hcore:B⁻¹ (.inl x) (.inl y)=
      (g.lowerDeficit (multiLeafMultiplicity mate) hr).extensionGreen q z x y:=
    congrArg (fun M:Matrix V V ℂ=>M x y) hN.2
  rw [hcore] at hh
  exact hh

end DeficientGraph
end LocalLaw
