import LocalLaw.LeafSchurModelRows
import LocalLaw.LeafCompletionAnalytic

/-! # Uniform separated endpoint rows for the actual leaf-deleted core -/

noncomputable section
set_option maxHeartbeats 2200000
namespace LocalLaw
local instance leafDeletedSeparatedDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def leafDeletedSeparatedRowCap (d : ℕ) (B : ℝ) : ℝ :=
  let W:=4*finiteExtraReferenceConstant d
  W+2*W*(2*|B|+3)*W

namespace DeficientGraph
variable {V I J : Type} [Fintype V] [Fintype I] [Fintype J] {d : ℕ}

theorem attachLeaves_weak_separated_rows (g : DeficientGraph V d) (hd : 3≤d)
    (mate : I→V) (other : J→V) (hrestore : ∀v,multiLeafMultiplicity mate v≤g.deficit v)
    (q z p : ℂ) (hz : 0<z.im) (hqim : 0≤q.im) (hq : q≠0) (hp0 : p≠0)
    (hp : p*(q⁻¹-q/((d:ℂ)-1))=1) :
    let H:=g.attachLeaves (by omega) mate hrestore
    ∀(_hbudget : H.ComponentFiniteReferenceBudget)(B C1 ε L A : ℝ)(_hzB : ‖z‖≤B)
    (r R : ℕ)(_num : SourceObservationBounds d r z B C1 ε L A)
    (_hprior : ‖q-semicircleRoot z‖≤C1*scalarScale (spectralScale z) ε)
    (_hR : ∀a b,H.graph.dist a b≤R)(_hRlog : (R:ℝ)+1≤A*L)
    (_htree : ∀l:I,(graphBall H.graph (.inr l) r).IsTree)
    (_hzero : ∀l:I,∀w∈graphBallVertices H.graph (.inr l) r,H.deficit w=0)
    (_hsep : ∀l k:I,l≠k→((2*r:ℕ):ℕ∞)<H.graph.edist (.inr l) (.inr k))
    (_hpbound : ‖p‖≤4)(_hqinv : ‖q⁻¹‖≤2*(B+1))(_hqpow : ∀n≤4*r+1,‖q‖^n≤2)
    (_hpinv : ‖p⁻¹‖≤2*|B|+3)
    (_hcount : (Fintype.card I:ℝ)*physicalTransfer d z^r≤1)
    (_hsmall : (Fintype.card I:ℝ)*‖p⁻¹‖*(leafCovarianceCoefficient d B A C1*L*ε)≤1/2)
    (_hOtherSep : ∀i j:J,i≠j→((2*r:ℕ):ℕ∞)<g.graph.edist (other i) (other j))
    (_hOtherCount : (Fintype.card J:ℝ)*physicalTransfer d z^r≤1),
    (∀x:V,(∑l:J,‖g.extensionGreen q z x (other l)‖)≤leafDeletedSeparatedRowCap d B) ∧
      (∀x:V,(∑l:J,‖g.extensionGreen q z (other l) x‖)≤leafDeletedSeparatedRowCap d B) := by
  dsimp only
  intro hbudget B C1 ε L A hzB r R num hprior hR hRlog htree hzero hsep hpbound hqinv hqpow
    hpinv hcount hsmall hOtherSep hOtherCount
  let H:=g.attachLeaves (by omega) mate hrestore
  let δ:=leafCovarianceCoefficient d B A C1*L*ε
  let W:=4*finiteExtraReferenceConstant d
  let P:=2*|B|+3
  have hL0 : 0≤L := (by norm_num:(0:ℝ)≤1).trans num.log_one
  have hscaled : 0≤C1^2*ε := mul_nonneg (sq_nonneg C1) num.error_nonnegative
  have hprior' := hprior.trans (scalarScale_constant_absorption (spectralScale z) ε C1
    (spectralScale_pos hz) num.error_nonnegative num.coefficient_one)
  have hfeedback:=(weak_localization_feedback_budgets d hd z q hz B (C1^2*ε) L A
    hscaled num.log_one num.log_cap_nonnegative num.error_scaled hprior'
    R (4*r+1) hRlog num.pair_log num.localization_large).1
  let e:I↪(V⊕I):={toFun:=Sum.inr,inj':=Sum.inr_injective}
  have hcov:=H.leaf_scalar_covariance hd hbudget e r R htree hzero
    (fun l k h=>(hsep l k h).le) q p z hq hp hz hqim B C1 ε L A hzB num hprior
    hR hRlog hpbound hqinv hqpow
  have hcoef : (treePatchWeakConstant d B A+2*finiteExtraReferenceConstant d)*C1^2*L*ε≤δ := by
    have hc : treePatchWeakConstant d B A+2*finiteExtraReferenceConstant d≤
        |treePatchWeakConstant d B A+2*finiteExtraReferenceConstant d|+1 := by
      linarith [le_abs_self (treePatchWeakConstant d B A+2*finiteExtraReferenceConstant d)]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc (sq_nonneg C1)) hL0) num.error_nonnegative
  have hδ : 0≤δ := mul_nonneg (mul_nonneg (leafCovarianceCoefficient_nonnegative d B A C1) hL0) num.error_nonnegative
  have hW : 0≤W := by dsimp only [W]; linarith [finiteExtraReferenceConstant_ge_one d hd]
  have hrows:=H.separated_target_leaf_rows hd hbudget (Sum.inr:I→V⊕I) r hsep q z hz hqim R hR hfeedback hcount
  have hsepOther (i j:J) (hij:i≠j) : ((2*r:ℕ):ℕ∞)<H.graph.edist (.inl (other i)) (.inl (other j)) := by
    change ((2*r:ℕ):ℕ∞)<(multiLeafGraph g.graph mate).edist (.inl (other i)) (.inl (other j))
    rw [multiLeafGraph_edist_old]
    exact hOtherSep i j hij
  have hother:=H.separated_target_leaf_rows hd hbudget (fun i:J=>Sum.inl (other i)) r hsepOther
    q z hz hqim R hR hfeedback hOtherCount
  have hout:=g.attachLeaves_remaining_rows_cols hd mate hrestore other q z p hz hqim hp0 δ W W W hδ hW
    (fun l k=>(hcov.2 l k).trans hcoef) hsmall (fun x=>hother.1 (.inl x))
    (fun x=>hrows.1 (.inl x)) (fun l=>hother.1 (.inr l))
  have hcap : W+2*W*‖p⁻¹‖*W≤leafDeletedSeparatedRowCap d B :=
    add_le_add_left
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpinv (by positivity:0≤2*W)) hW) W
  exact ⟨fun x=>(hout.1 x).trans hcap,fun x=>(hout.2 x).trans hcap⟩

end DeficientGraph
end LocalLaw
