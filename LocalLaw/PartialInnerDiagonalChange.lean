import LocalLaw.PartialInnerAmbient
import LocalLaw.OneSidedDiagonalComparison

/-! Exact omitted-T diagonal change, finite boundary mass and one-sided bound. -/
open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance partialInnerDiagonalChangeDecidable (p:Prop):Decidable p:=Classical.propDecidable p
set_option maxHeartbeats 2000000
namespace DeficientGraph
variable {V:Type}[Fintype V]{d:ℕ}

theorem partialInnerAmbient_restrict_matrix_difference [DecidableEq V]
    (g:DeficientGraph V d)(T S:Set V)(K:Set (Tᶜ:Set V))(q z:ℂ):
    ((g.partialInnerAmbient T S).restrict K).extensionMatrix q z-
      ((g.delete T).restrict K).extensionMatrix q z=
      Matrix.diagonal (fun v:K=>-q*(((g.partialInnerOmittedCharge T S v.val:ℝ)/((d:ℝ)-1)):ℂ)):=by
  let M:=(g.delete T).restrict K
  let ρ:K→ℕ:=fun v=>g.partialInnerOmittedCharge T S v.val
  have hρ:∀v,ρ v≤M.deficit v:=fun v=>g.partialInnerOmittedCharge_le T S v.val
  change (M.lowerDeficit ρ hρ).extensionMatrix q z-M.extensionMatrix q z=_
  rw [M.lowerDeficit_extensionMatrix]
  ext i j
  by_cases hij:i=j
  · subst j
    simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,Matrix.diagonal_apply_eq]
    ring
  · simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,Matrix.diagonal_apply,hij,if_false,mul_zero]
    ring

theorem partialInnerOmittedCharge_sum_le_boundary (g:DeficientGraph V d)(T S:Set V)(K:Set (Tᶜ:Set V)):
    (∑v:K,g.partialInnerOmittedCharge T S v.val)≤Nat.card (BoundaryOrientedEdge g.graph T):=by
  let I:=Σv:K,{t:T//t.val∉S∧g.graph.Adj t.val v.val.val}
  let f:I→BoundaryOrientedEdge g.graph T:=
    fun u=>⟨(u.2.val.val,u.1.val.val),u.2.property.2,u.2.val.property,u.1.val.property⟩
  have hf:Function.Injective f:=by
    rintro ⟨v,t⟩ ⟨w,u⟩ h
    have hp:=congrArg (fun e:BoundaryOrientedEdge g.graph T=>e.val) h
    have hv:v=w:=Subtype.ext (Subtype.ext (congrArg Prod.snd hp))
    subst w
    have ht:t=u:=Subtype.ext (Subtype.ext (congrArg Prod.fst hp))
    subst u
    rfl
  have hh:=Nat.card_le_card_of_injective f hf
  rw [Nat.card_sigma] at hh
  exact hh


theorem partialInnerOmittedCharge_pair_depth (g:DeficientGraph V d)(T:Set V)(x y:V)(r:ℕ)
    (v:{v:(Tᶜ:Set V)|v.val∈pairBallVertices g.graph x y r})
    (hv:g.partialInnerOmittedCharge T (pairBallVertices g.graph x y r) v.val≠0):
    (r:ℕ∞)≤g.graph.edist x v.val.val ∧ (r:ℕ∞)≤g.graph.edist y v.val.val:=by
  have he:∃t:T,t.val∉pairBallVertices g.graph x y r ∧ g.graph.Adj t.val v.val.val:=by
    by_cases hn:Nonempty {t:T//t.val∉pairBallVertices g.graph x y r ∧ g.graph.Adj t.val v.val.val}
    · obtain ⟨t⟩:=hn
      exact ⟨t.val,t.property⟩
    · haveI:IsEmpty {t:T//t.val∉pairBallVertices g.graph x y r ∧ g.graph.Adj t.val v.val.val}:=
        not_nonempty_iff.mp hn
      exact False.elim (hv (by simp [partialInnerOmittedCharge]))
  exact omitted_neighbor_pair_boundary_depth g.graph x y r T ⟨v.val.val,v.property⟩ he

theorem partialInnerOmittedCharge_norm_mass (g:DeficientGraph V d)(hd:3≤d)
    (T S:Set V)(K:Set (Tᶜ:Set V))(q:ℂ):
    (∑v:K,‖-q*(((g.partialInnerOmittedCharge T S v.val:ℝ)/((d:ℝ)-1)):ℂ)‖)≤
      (‖q‖/((d:ℝ)-1))*(Nat.card (BoundaryOrientedEdge g.graph T):ℝ):=by
  have hdR:(3:ℝ)≤d:=Nat.cast_le.mpr hd
  have hk:0<(d:ℝ)-1:=by linarith
  have hden:‖(d:ℂ)-1‖=(d:ℝ)-1:=by
    have hc:(d:ℂ)-1=(((d:ℝ)-1:ℝ):ℂ):=by push_cast;rfl
    rw [hc,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hk]
  have he (v:K):‖-q*(((g.partialInnerOmittedCharge T S v.val:ℝ)/((d:ℝ)-1)):ℂ)‖=
      (‖q‖/((d:ℝ)-1))*(g.partialInnerOmittedCharge T S v.val:ℝ):=by
    simp only [norm_mul,norm_neg,norm_div,Complex.ofReal_natCast,Complex.norm_natCast,Complex.ofReal_one]
    rw [hden]
    ring
  simp_rw [he]
  rw [←Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (div_nonneg (norm_nonneg _) hk.le)
  exact_mod_cast g.partialInnerOmittedCharge_sum_le_boundary T S K

theorem partialInnerAmbient_one_sided_change [DecidableEq V]
    (g:DeficientGraph V d)(hd:3≤d)(T S:Set V)(K:Set (Tᶜ:Set V))
    (q z:ℂ)(hz:0<z.im)(hq:0≤q.im)(x y:K)(F C:ℝ)(hF:0≤F)(hC:0≤C)
    (hupper:∀v:K,g.partialInnerOmittedCharge T S v.val≠0→
      ‖((g.delete T).restrict K).extensionGreen q z x v‖≤F)
    (hlower:∀v:K,‖((g.partialInnerAmbient T S).restrict K).extensionGreen q z v y‖≤C):
    ‖((g.delete T).restrict K).extensionGreen q z x y-
      ((g.partialInnerAmbient T S).restrict K).extensionGreen q z x y‖≤
      F*C*(‖q‖/((d:ℝ)-1))*(Nat.card (BoundaryOrientedEdge g.graph T):ℝ):=by
  let A:=((g.delete T).restrict K).extensionMatrix q z
  let B:=((g.partialInnerAmbient T S).restrict K).extensionMatrix q z
  let e:K→ℂ:=fun v=>-q*(((g.partialInnerOmittedCharge T S v.val:ℝ)/((d:ℝ)-1)):ℂ)
  have hchange:B-A=Matrix.diagonal e:=g.partialInnerAmbient_restrict_matrix_difference T S K q z
  have hh:=inverse_diagonal_change_one_sided A B
    (((g.delete T).restrict K).extensionMatrix_isUnit hd q z hz hq)
    (((g.partialInnerAmbient T S).restrict K).extensionMatrix_isUnit hd q z hz hq)
    e hchange x y F C hF hC (fun v hv=>hupper v (by
      intro hzero
      apply hv
      simp only [e,hzero,Nat.cast_zero,zero_div,Complex.ofReal_zero,mul_zero]))
    (fun v _=>hlower v)
  have hm:=g.partialInnerOmittedCharge_norm_mass hd T S K q
  exact hh.trans ((mul_le_mul_of_nonneg_left hm (mul_nonneg hF hC)).trans_eq (by ring))

end DeficientGraph
end LocalLaw
