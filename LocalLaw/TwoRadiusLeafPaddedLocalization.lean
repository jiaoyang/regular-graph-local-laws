import LocalLaw.LeafPaddedLocalization
import LocalLaw.TwoRadiusLeafLocalization
import LocalLaw.TwoRadiusSchurProducts
import LocalLaw.ScalarLeafPadding

/-! # Actual two-radius localization products on the common leaf index

The local leaf vectors are padded by zero outside the restriction.  The
asymmetric tail is recovered by the opposite Green factor for retained
leaves. Omitted leaves are far from both targets. Unreachable leaves give
an exactly zero product, so natural graph distance is never used there.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2200000
namespace LocalLaw
local instance twoRadiusLeafPaddedDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace DeficientGraph
variable {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I] {d : ℕ}

omit [DecidableEq I] in
theorem leaf_padded_localization_products_two_radii (g : DeficientGraph V d) (hd : 3≤d)
    (hbudget : g.ComponentFiniteReferenceBudget) (S : Set V) (e : I→V)
    (q z : ℂ) (hz : 0<z.im) (hq : 0≤q.im) (B : ℝ) (hzB : ‖z‖≤B)
    (ε L A : ℝ) (hε : 0≤ε) (hεOne : ε≤1) (hL : 1≤L) (hA : 0≤A) (hcap : ε*L^4≤1)
    (hprior : ‖q-semicircleRoot z‖≤scalarScale (spectralScale z) ε)
    (R Rs : ℕ) (hR : ∀ a b,g.graph.dist a b≤R) (hRs : ∀ a b,(g.restrict S).graph.dist a b≤Rs)
    (hRlog : (R:ℝ)+1≤A*L) (hRslog : (Rs:ℝ)+1≤A*L)
    (hlarge : localizationBudgetConstant d B A≤L)
    (i j : S) (ri rj : ℕ)
    (hI : graphBallVertices g.graph i.val ri⊆S) (hJ : graphBallVertices g.graph j.val rj⊆S)
    (Aw Bw : ℝ)
    (hAw : (∑l:{l:I | e l∈S},‖(g.restrict S).extensionGreen q z i ⟨e l.val,l.property⟩‖)≤Aw)
    (hBw : (∑l:I,‖g.extensionGreen q z (e l) j.val‖)≤Bw) :
    let E : Set I:={l | e l∈S}
    let P:=g.extensionGreen q z
    let Q:=(g.restrict S).extensionGreen q z
    let a':=scalarLeafPaddedVector E (fun l=>Q i ⟨e l.val,l.property⟩)
    let b':=scalarLeafPaddedVector E (fun l=>Q ⟨e l.val,l.property⟩ j)
    let u:=2*localizationFeedbackConstant d B A*L*ε
    let v:=localizationTailConstant d
    let C:=2*finiteExtraReferenceConstant d
    let ρ:=physicalTransfer d z
    (∑l:I,‖P i.val (e l)*P (e l) j.val-a' l*b' l‖)≤
      u*(Bw+Aw)+(2*v*C+C^2)*(Fintype.card I:ℝ)*ρ^(ri+rj) := by
  classical
  dsimp only
  let E : Set I:={l | e l∈S}
  let P:=g.extensionGreen q z
  let Q:=(g.restrict S).extensionGreen q z
  let a':=scalarLeafPaddedVector E (fun l=>Q i ⟨e l.val,l.property⟩)
  let b':=scalarLeafPaddedVector E (fun l=>Q ⟨e l.val,l.property⟩ j)
  let u:=2*localizationFeedbackConstant d B A*L*ε
  let v:=localizationTailConstant d
  let C:=2*finiteExtraReferenceConstant d
  let ρ:=physicalTransfer d z
  have hρ:0≤ρ:=(physicalTransfer_pos d hd z).le
  have hρone:ρ≤1:=by dsimp only [ρ]; nlinarith [physicalTransfer_sq_le_half d hd z]
  have hu:0≤u:=by
    have hc:=coreConvolutionConstant_nonnegative (finiteOmega d+1)
    dsimp only [u,localizationFeedbackConstant]
    positivity
  have hC:0≤C:=by dsimp only [C]; have hh:=finiteExtraReferenceConstant_ge_one d hd; positivity
  have hv:0≤v:=by
    have hD:0<(d:ℝ)-1:=by have hh: (3:ℝ)≤d:=Nat.cast_le.mpr hd; linarith
    have hc:=finiteExtraReferenceConstant_ge_one d hd
    dsimp only [v,localizationTailConstant,localizationExceptionalMass]
    positivity
  have htail:0≤(2*v*C+C^2)*ρ^(ri+rj):=by positivity
  obtain ⟨sG,sS,_⟩:=weak_localization_feedback_budgets d hd z q hz B ε L A hε hL hA hcap hprior
    R Rs hRlog hRslog hlarge
  have heq (l:I) (hl:e l∈S) :
      a' l=Q i ⟨e l,hl⟩ ∧ b' l=Q ⟨e l,hl⟩ j := by
    dsimp only [a',b',scalarLeafPaddedVector]
    rw [Equiv.Set.sumCompl_symm_apply_of_mem (show l∈E from hl)]
    exact ⟨rfl,rfl⟩
  have hzero (l:I) (hl:e l∉S) : a' l=0 ∧ b' l=0 := by
    dsimp only [a',b',scalarLeafPaddedVector]
    rw [Equiv.Set.sumCompl_symm_apply_of_not_mem (show l∉E from hl)]
    exact ⟨rfl,rfl⟩
  have hlocalzero (x:S) (l:I) (hl:e l∈S) (hn:¬g.graph.Reachable x.val (e l)) :
      Q x ⟨e l,hl⟩=0 := by
    apply (g.restrict S).extensionGreen_zero_of_not_reachable hd q z hz hq
    intro hr
    exact hn (hr.map (SimpleGraph.Embedding.induce S).toHom)
  have hpoint (l:I) :
      ‖P i.val (e l)*P (e l) j.val-a' l*b' l‖≤
        u*(‖P (e l) j.val‖+‖a' l‖)+(2*v*C+C^2)*ρ^(ri+rj) := by
    by_cases hi:g.graph.Reachable i.val (e l)
    · by_cases hj:g.graph.Reachable j.val (e l)
      · by_cases hl:e l∈S
        · obtain ⟨hea,heb,hbdecay,hadecay⟩:=g.leaf_localization_factors_two_radii hd hbudget S q z hz hq B hzB
            ε L A hε hεOne hL hA hcap hprior R Rs hR hRs hRlog hRslog hlarge
            i j ⟨e l,hl⟩ ri rj hi hj hI hJ
          obtain ⟨ha',hb'⟩:=heq l hl
          rw [ha',hb']
          have hh:=two_radius_product_difference_bound (P i.val (e l)) (P (e l) j.val)
            (Q i ⟨e l,hl⟩) (Q ⟨e l,hl⟩ j) ρ u v C hρ hρone hv hC
            (ri+twoRadiusLeafRadius ri rj (g.graph.dist i.val (e l)) (g.graph.dist j.val (e l)))
            (rj+twoRadiusLeafRadius ri rj (g.graph.dist i.val (e l)) (g.graph.dist j.val (e l)))
            (g.graph.dist i.val (e l)) (g.graph.dist j.val (e l)) (ri+rj)
            (by unfold twoRadiusLeafRadius;omega) (by unfold twoRadiusLeafRadius;omega)
            hea heb hadecay hbdecay
          exact hh.trans (by nlinarith [mul_nonneg (sq_nonneg C) (pow_nonneg hρ (ri+rj))])
        · obtain ⟨ha',hb'⟩:=hzero l hl
          rw [ha',hb',zero_mul,sub_zero]
          have hdi:ri≤g.graph.dist i.val (e l):=by
            by_contra hn
            apply hl
            apply hI
            have he:(g.graph.dist i.val (e l):ℕ∞)=g.graph.edist i.val (e l):=
              ENat.coe_toNat (SimpleGraph.edist_ne_top_iff_reachable.mpr hi)
            exact he.ge.trans (ENat.coe_le_coe.mpr (by omega))
          have hdj:rj≤g.graph.dist j.val (e l):=by
            by_contra hn
            apply hl
            apply hJ
            have he:(g.graph.dist j.val (e l):ℕ∞)=g.graph.edist j.val (e l):=
              ENat.coe_toNat (SimpleGraph.edist_ne_top_iff_reachable.mpr hj)
            exact he.ge.trans (ENat.coe_le_coe.mpr (by omega))
          have hka:=g.componentwise_finite_kernel_decay hd hbudget q z hz hq R hR sG i.val (e l)
          have hkb:=g.componentwise_finite_kernel_decay hd hbudget q z hz hq R hR sG j.val (e l)
          have hh:=omitted_two_radius_product_bound (P i.val (e l)) (P j.val (e l)) ρ C hρ hρone hC
            (g.graph.dist i.val (e l)) (g.graph.dist j.val (e l)) (ri+rj) (by omega) hka hkb
          have hs:P (e l) j.val=P j.val (e l):=(g.extensionGreen_isSymm q z).apply j.val (e l)
          rw [hs]
          exact hh.trans (by
            have hn:=mul_nonneg hu (add_nonneg (norm_nonneg (P j.val (e l))) (norm_nonneg (0:ℂ)))
            have ht:=mul_nonneg (mul_nonneg hv hC) (pow_nonneg hρ (ri+rj))
            norm_num only [norm_zero,add_zero] at hn ⊢
            nlinarith only [hn,ht])
      · have hzP:P (e l) j.val=0:=by
          rw [show P (e l) j.val=P j.val (e l) from (g.extensionGreen_isSymm q z).apply j.val (e l)]
          exact g.extensionGreen_zero_of_not_reachable hd q z hz hq _ _ hj
        have hzQ:b' l=0:=by
          by_cases hl:e l∈S
          · rw [(heq l hl).2]
            rw [show Q ⟨e l,hl⟩ j=Q j ⟨e l,hl⟩ from ((g.restrict S).extensionGreen_isSymm q z).apply j ⟨e l,hl⟩]
            exact hlocalzero j l hl hj
          · exact (hzero l hl).2
        rw [hzP,hzQ,mul_zero,mul_zero,sub_self,norm_zero]
        positivity
    · have hzP:P i.val (e l)=0:=g.extensionGreen_zero_of_not_reachable hd q z hz hq _ _ hi
      have hzQ:a' l=0:=by
        by_cases hl:e l∈S
        · rw [(heq l hl).1]; exact hlocalzero i l hl hi
        · exact (hzero l hl).1
      rw [hzP,hzQ,zero_mul,zero_mul,sub_self,norm_zero]
      positivity
  have hAw':(∑l:I,‖a' l‖)≤Aw:=by
    rw [show (∑l:I,‖a' l‖)=∑l:E,‖Q i ⟨e l.val,l.property⟩‖ from scalarLeafPaddedVector_sum_norm E _]
    exact hAw
  calc
    _≤∑l:I,(u*(‖P (e l) j.val‖+‖a' l‖)+(2*v*C+C^2)*ρ^(ri+rj)):=
      Finset.sum_le_sum (fun l _=>hpoint l)
    _=u*((∑l:I,‖P (e l) j.val‖)+(∑l:I,‖a' l‖))+
        (Fintype.card I:ℝ)*((2*v*C+C^2)*ρ^(ri+rj)):=by
      rw [Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_add_distrib]
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    _≤u*(Bw+Aw)+(Fintype.card I:ℝ)*((2*v*C+C^2)*ρ^(ri+rj)):=
      add_le_add_right (mul_le_mul_of_nonneg_left (add_le_add hBw hAw') hu) _
    _=_:=by ring

end DeficientGraph
end LocalLaw
