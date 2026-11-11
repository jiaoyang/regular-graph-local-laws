import LocalLaw.RestrictedTreePatchResidual
import LocalLaw.WeakQuadraticResidual
import LocalLaw.SourceSingletonObservation

/-! # Logarithmic tree-patch error under the actual weak scalar prior -/

noncomputable section
namespace LocalLaw
local instance treePatchWeakResidualDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def treePatchWeakConstant (d : ℕ) (B A : ℝ) : ℝ :=
  DeficientGraph.localizationWeakConstant d B A+
    2*(B+1)*(Real.sqrt (B+2)+1)*(8*finiteExtraReferenceConstant d^2+128)*A

namespace DeficientGraph
variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

theorem restrict_tree_pair_weak_residual (g : DeficientGraph V d) (hd : 3≤d)
    (S : Set V) (hbudget : (g.restrict S).ComponentFiniteReferenceBudget)
    (u v : S) (r k R : ℕ) (hcenters : g.graph.edist u.val v.val≤(k:ℕ∞))
    (htree : (graphBall g.graph u.val (r+k)).IsTree)
    (hzero : ∀ w∈graphBallVertices g.graph u.val (r+k),g.deficit w=0)
    (q p z : ℂ) (hq : q≠0) (hp : p*(q⁻¹-q/((d:ℂ)-1))=1)
    (hz : 0<z.im) (hqim : 0 ≤ q.im) (B C ε L A : ℝ) (hzB : ‖z‖≤B)
    (num : SourceObservationBounds d r z B C ε L A)
    (hprior : ‖q-semicircleRoot z‖≤C*scalarScale (spectralScale z) ε)
    (hR : ∀ a b,(g.restrict S).graph.dist a b≤R) (hRlog : (R:ℝ)+1≤A*L)
    (hpbound : ‖p‖≤4) (hqinv : ‖q⁻¹‖≤2*(B+1))
    (hqpow : ∀ n≤4*r+1,‖q‖^n≤2) :
    let M := g.restrict S
    let K := M.restrict (pairBallVertices M.graph u v r)
    ‖M.extensionGreen q z u v-formalForestKernel K.graph d q p
      (pairBallLeft M.graph u v r) (pairBallRight M.graph u v r)‖≤
      treePatchWeakConstant d B A*C^2*L*ε := by
  dsimp only
  have hB : 0≤B := (norm_nonneg z).trans hzB
  have hscaled : 0≤C^2*ε := mul_nonneg (sq_nonneg C) num.error_nonnegative
  have hprior' := hprior.trans (scalarScale_constant_absorption (spectralScale z) ε C
    (spectralScale_pos hz) num.error_nonnegative num.coefficient_one)
  have htail := num.tail
  have hlocal := (g.restrict S).componentwise_weak_pair_localization hd hbudget q z hz hqim B hzB
    (C^2*ε) L A hscaled num.log_one num.log_cap_nonnegative num.error_scaled hprior'
    R r hR hRlog num.pair_log num.localization_large htail u v
  have hsmall := (weak_localization_feedback_budgets d hd z q hz B (C^2*ε) L A
    hscaled num.log_one num.log_cap_nonnegative num.error_scaled hprior'
    R (4*r+1) hRlog num.pair_log num.localization_large).2.1
  have hpair := g.restrict_P_formal_forest_error hd S hbudget u v r k hcenters htree hzero
    q p z hq hp hz hqim hsmall 4 2 (by norm_num) (by norm_num) hpbound hqpow
  dsimp only at hpair
  have hres := weak_prior_quadratic_defect_div q z hz B (C^2*ε) (2*(B+1)) hzB hscaled hprior'
    (by positivity) hqinv
  have hC : 0≤8*finiteExtraReferenceConstant d^2+128 := by positivity
  have hR0 : 0≤((4*r+1:ℕ)+1:ℝ) := by positivity
  have hresC := mul_le_mul_of_nonneg_right hres hC
  have hresR := mul_le_mul_of_nonneg_right hresC hR0
  have hpair' :
      ‖(g.restrict S).P r z q u v-formalForestKernel
        ((g.restrict S).restrict (pairBallVertices (g.restrict S).graph u v r)).graph d q p
        (pairBallLeft (g.restrict S).graph u v r) (pairBallRight (g.restrict S).graph u v r)‖≤
        (2*(B+1)*(Real.sqrt (B+2)+1)*(8*finiteExtraReferenceConstant d^2+128)*A)*L*(C^2*ε) := by
    apply hpair.trans
    norm_num only [Nat.reduceAdd,Nat.reduceMul,OfNat.ofNat] at hresR ⊢
    apply hresR.trans
    have hlen := mul_le_mul_of_nonneg_left num.pair_log
      (show 0≤2*(B+1)*(Real.sqrt (B+2)+1)*(C^2*ε)*(8*finiteExtraReferenceConstant d^2+128) by positivity)
    convert hlen using 1; ring
  exact ((norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hlocal hpair')).trans_eq
    (by unfold treePatchWeakConstant; ring)

end DeficientGraph
end LocalLaw
