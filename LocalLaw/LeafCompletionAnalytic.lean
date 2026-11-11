import LocalLaw.LeafSchurLocalization
import LocalLaw.GlobalLeafScalarCovariance
import LocalLaw.SeparatedTargetLeafRows

/-! # Leaf completion comparison with all covariance and weight bounds derived -/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2500000
namespace LocalLaw
local instance leafCompletionAnalyticDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def leafCovarianceCoefficient (d : ℕ) (B A C1 : ℝ) : ℝ :=
  (|treePatchWeakConstant d B A+2*finiteExtraReferenceConstant d|+1)*C1^2

theorem leafCovarianceCoefficient_nonnegative (d : ℕ) (B A C1 : ℝ) :
    0≤leafCovarianceCoefficient d B A C1 := by unfold leafCovarianceCoefficient; positivity

namespace DeficientGraph
variable {V I : Type} [Fintype V] [Fintype I] {d : ℕ}

theorem attachLeaves_weak_localization (g : DeficientGraph V d) (hd : 3≤d)
    (mate : I→V) (hrestore : ∀v,multiLeafMultiplicity mate v≤g.deficit v)
    (S : Set V) (q z p : ℂ) (hz : 0<z.im) (hqim : 0≤q.im) (hq : q≠0) (hp0 : p≠0)
    (hp : p*(q⁻¹-q/((d:ℂ)-1))=1) :
    let H:=g.attachLeaves (by omega) mate hrestore
    let U:=multiLeafLift mate S
    ∀(hbudget : H.ComponentFiniteReferenceBudget)(B C1 ε L A : ℝ)(hzB : ‖z‖≤B)
    (r R Rs : ℕ)(num : SourceObservationBounds d r z B C1 ε L A)
    (hprior : ‖q-semicircleRoot z‖≤C1*scalarScale (spectralScale z) ε)
    (hR : ∀a b,H.graph.dist a b≤R)(hRs : ∀a b,(H.restrict U).graph.dist a b≤Rs)
    (hRlog : (R:ℝ)+1≤A*L)(hRslog : (Rs:ℝ)+1≤A*L)
    (htree : ∀l:I,(graphBall H.graph (.inr l) r).IsTree)
    (hzero : ∀l:I,∀w∈graphBallVertices H.graph (.inr l) r,H.deficit w=0)
    (hsep : ∀l k:I,l≠k→((2*r:ℕ):ℕ∞)<H.graph.edist (.inr l) (.inr k))
    (hpbound : ‖p‖≤4)(hqinv : ‖q⁻¹‖≤2*(B+1))(hqpow : ∀n≤4*r+1,‖q‖^n≤2)
    (hcount : (Fintype.card I:ℝ)*physicalTransfer d z^r≤1)
    (hsmall : (Fintype.card I:ℝ)*‖p⁻¹‖*(leafCovarianceCoefficient d B A C1*L*ε)≤1/2)
    (i j : S)(hI : graphBallVertices H.graph (.inl i.val) r⊆U)
    (hJ : graphBallVertices H.graph (.inl j.val) r⊆U),
    let u:=2*localizationFeedbackConstant d B A*L*(C1^2*ε)
    let v:=localizationTailConstant d
    let C:=2*finiteExtraReferenceConstant d
    let W:=4*finiteExtraReferenceConstant d
    let ρ:=physicalTransfer d z
    ‖g.extensionGreen q z i.val j.val-(g.restrict S).extensionGreen q z i j‖≤
      u+v*ρ^(2*r)+‖p⁻¹‖*(2*u*W+(2*v*C+C^2)*(Fintype.card I:ℝ)*ρ^(2*r))+
        4*‖p⁻¹‖^2*(leafCovarianceCoefficient d B A C1*L*ε)*W^2 := by
  dsimp only
  intro hbudget B C1 ε L A hzB r R Rs num hprior hR hRs hRlog hRslog htree hzero hsep
    hpbound hqinv hqpow hcount hsmall i j hI hJ
  let H:=g.attachLeaves (by omega) mate hrestore
  let U:=multiLeafLift mate S
  let E : Set I:={l |mate l∈S}
  let P:=H.extensionGreen q z
  let Q:=(H.restrict U).extensionGreen q z
  let δleaf:=leafCovarianceCoefficient d B A C1*L*ε
  let W:=4*finiteExtraReferenceConstant d
  have hL0 : 0≤L := (by norm_num:(0:ℝ)≤1).trans num.log_one
  have hscaled : 0≤C1^2*ε := mul_nonneg (sq_nonneg _) num.error_nonnegative
  have hprior' := hprior.trans (scalarScale_constant_absorption (spectralScale z) ε C1
    (spectralScale_pos hz) num.error_nonnegative num.coefficient_one)
  have hεOne : C1^2*ε≤1 := (le_mul_of_one_le_right hscaled (one_le_pow₀ num.log_one)).trans num.error_scaled
  have hδ : 0≤δleaf := by dsimp only [δleaf]; exact mul_nonneg (mul_nonneg
    (leafCovarianceCoefficient_nonnegative d B A C1) hL0) num.error_nonnegative
  have hW : 0≤W := by dsimp only [W]; have hh:=finiteExtraReferenceConstant_ge_one d hd; positivity
  have hbLocal:=H.restrict_componentFiniteReferenceBudget U hbudget
  have hfeedback:=weak_localization_feedback_budgets d hd z q hz B (C1^2*ε) L A
    hscaled num.log_one num.log_cap_nonnegative num.error_scaled hprior' R Rs hRlog hRslog num.localization_large
  let he: I↪(V⊕I):={toFun:=Sum.inr,inj':=Sum.inr_injective}
  have hcovG:=H.leaf_scalar_covariance hd hbudget he r R htree hzero
    (fun l k h=> (hsep l k h).le) q p z hq hp hz hqim B C1 ε L A hzB num hprior
    hR hRlog hpbound hqinv hqpow
  have hcovS:=H.restricted_leaf_scalar_covariance hd U hbLocal (multiLeafLiftLeaf mate S) r Rs
    (fun l=>htree l.val) (fun l=>hzero l.val)
    (fun l k h=> (hsep l.val k.val (fun heq=>h (Subtype.ext heq))).le)
    q p z hq hp hz hqim B C1 ε L A hzB num hprior hRs hRslog hpbound hqinv hqpow
  have hcoef : (treePatchWeakConstant d B A+2*finiteExtraReferenceConstant d)*C1^2*L*ε≤δleaf := by
    have hbase : treePatchWeakConstant d B A+2*finiteExtraReferenceConstant d≤
        |treePatchWeakConstant d B A+2*finiteExtraReferenceConstant d|+1 := by
      linarith [le_abs_self (treePatchWeakConstant d B A+2*finiteExtraReferenceConstant d)]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hbase (sq_nonneg _)) hL0) num.error_nonnegative
  have hrowsG:=H.separated_target_leaf_rows hd hbudget (Sum.inr:I→V⊕I) r hsep q z hz hqim
    R hR hfeedback.1 hcount
  have hlocalSep (l k:E) (h:l≠k) : ((2*r:ℕ):ℕ∞)<(H.restrict U).graph.edist
      (multiLeafLiftLeaf mate S l) (multiLeafLiftLeaf mate S k) :=
    (hsep l.val k.val (fun heq=>h (Subtype.ext heq))).trans_le
      (ambient_edist_le_induced_edist H.graph U (multiLeafLiftLeaf mate S l) (multiLeafLiftLeaf mate S k))
  have hc : (Fintype.card E:ℝ)≤(Fintype.card I:ℝ) := by
    exact_mod_cast Fintype.card_le_of_injective (Subtype.val:E→I) Subtype.val_injective
  have hcountS : (Fintype.card E:ℝ)*physicalTransfer d z^r≤1 :=
    (mul_le_mul_of_nonneg_right hc (pow_nonneg (physicalTransfer_pos d hd z).le r)).trans hcount
  have hrowsS:=(H.restrict U).separated_target_leaf_rows hd hbLocal (multiLeafLiftLeaf mate S) r
    hlocalSep q z hz hqim Rs hRs hfeedback.2.1 hcountS
  exact g.attachLeaves_restriction_localization_bound hd mate hrestore S q z p hz hqim hp0
    hbudget B hzB (C1^2*ε) L A hscaled hεOne num.log_one num.log_cap_nonnegative num.error_scaled hprior'
    R Rs hR hRs hRlog hRslog num.localization_large i j r hI hJ δleaf W hδ hW
    (hrowsG.1 (.inl i.val)) (hrowsG.2 (.inl j.val))
    (hrowsS.1 (multiLeafLiftCore mate S i)) (hrowsS.2 (multiLeafLiftCore mate S j))
    (fun l k=>(hcovG.2 l k).trans hcoef) (fun l k=>(hcovS.2 l k).trans hcoef) hsmall

end DeficientGraph
end LocalLaw
