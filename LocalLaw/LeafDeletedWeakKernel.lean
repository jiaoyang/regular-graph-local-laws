import LocalLaw.LeafDeletedKernelDecay
import LocalLaw.LeafCompletionAnalytic

/-! # Weak-prior kernel decay for the actual leaf-deleted core -/

noncomputable section
set_option maxHeartbeats 2200000
namespace LocalLaw
local instance leafDeletedWeakKernelDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def leafDeletedCoreDecayConstant (d : ℕ) (B A C1 : ℝ) : ℝ :=
  let C:=2*finiteExtraReferenceConstant d
  let P:=2*|B|+3
  let W:=4*finiteExtraReferenceConstant d
  C+P*C^2*coreConvolutionConstant (finiteOmega d+1)*A+
    2*P^2*leafCovarianceCoefficient d B A C1*W^2

theorem leafDeletedCoreDecayConstant_nonnegative (d : ℕ) (hd : 3≤d) (B A C1 : ℝ) (hA : 0≤A) :
    0≤leafDeletedCoreDecayConstant d B A C1 := by
  have hC:=finiteExtraReferenceConstant_ge_one d hd
  have hConv:=coreConvolutionConstant_nonnegative (finiteOmega d+1)
  have hδ:=leafCovarianceCoefficient_nonnegative d B A C1
  unfold leafDeletedCoreDecayConstant
  positivity

namespace DeficientGraph
variable {V I : Type} [Fintype V] [Fintype I] {d : ℕ}

theorem attachLeaves_weak_edist_decay (g : DeficientGraph V d) (hd : 3≤d)
    (mate : I→V) (hrestore : ∀v,multiLeafMultiplicity mate v≤g.deficit v)
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
    (x y : V)(h : ℕ)(_hfar : (h:ℕ∞)≤g.graph.edist x y),
    ‖g.extensionGreen q z x y‖≤leafDeletedCoreDecayConstant d B A C1*L*physicalTransfer d z^h+
      leafDeletedCoreDecayConstant d B A C1*L*ε := by
  dsimp only
  intro hbudget B C1 ε L A hzB r R num hprior hR hRlog htree hzero hsep hpbound hqinv hqpow
    hpinv hcount hsmall x y h hfar
  let H:=g.attachLeaves (by omega) mate hrestore
  let δ:=leafCovarianceCoefficient d B A C1*L*ε
  let W:=4*finiteExtraReferenceConstant d
  let C:=2*finiteExtraReferenceConstant d
  let P:=2*|B|+3
  let Conv:=coreConvolutionConstant (finiteOmega d+1)
  let Dc:=C+P*C^2*Conv*A
  let Ec:=2*P^2*leafCovarianceCoefficient d B A C1*W^2
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
  have hC : 0≤C := by dsimp only [C]; linarith [finiteExtraReferenceConstant_ge_one d hd]
  have hP : 0≤P := by dsimp only [P]; positivity
  have hConv : 0≤Conv := coreConvolutionConstant_nonnegative _
  have hDc : 0≤Dc := by have hA:=num.log_cap_nonnegative;dsimp only [Dc]; positivity
  have hEc : 0≤Ec := by dsimp only [Ec]; have hh:=leafCovarianceCoefficient_nonnegative d B A C1;positivity
  have hrows:=H.separated_target_leaf_rows hd hbudget (Sum.inr:I→V⊕I) r hsep q z hz hqim R hR hfeedback hcount
  have hout:=g.attachLeaves_core_edist_decay hd mate hrestore q z p hz hqim hp0 hbudget R hR hfeedback
    δ W hδ hW (fun l k=>(hcov.2 l k).trans hcoef) hsmall (fun a=>hrows.1 (.inl a)) x y h hfar
  have hmain : C+‖p⁻¹‖*C^2*Conv*((R:ℝ)+1)≤Dc*L := by
    calc
      _≤C*L+P*C^2*Conv*(A*L) := by
        apply add_le_add
        · exact le_mul_of_one_le_right hC num.log_one
        · gcongr
      _=Dc*L := by dsimp only [Dc];ring
  have herr : 2*‖p⁻¹‖^2*δ*W^2≤Ec*L*ε := by
    calc
      _≤2*P^2*δ*W^2 := by gcongr
      _=Ec*L*ε := by dsimp only [Ec,δ];ring
  have hdecay : Dc≤Dc+Ec := le_add_of_nonneg_right hEc
  have herror : Ec≤Dc+Ec := le_add_of_nonneg_left hDc
  exact hout.trans ((add_le_add
    ((mul_le_mul_of_nonneg_right hmain (pow_nonneg (physicalTransfer_pos d hd z).le h)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hdecay hL0) (pow_nonneg (physicalTransfer_pos d hd z).le h)))
    (herr.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right herror hL0) num.error_nonnegative))).trans_eq (by rfl))

end DeficientGraph
end LocalLaw
