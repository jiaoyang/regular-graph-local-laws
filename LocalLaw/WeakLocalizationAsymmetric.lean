import LocalLaw.ComponentLocalizationAsymmetric
import LocalLaw.LocalizationFeedbackRate

/-! # Weak-prior asymmetric localization with its two-sided tail retained -/
noncomputable section
namespace LocalLaw
local instance weakLocalizationAsymmetricDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace DeficientGraph

theorem asymmetricLocalizationBound_feedback (d : ℕ) (hd : 3≤d)
    (z q : ℂ) (B L A : ℝ) (R ri rj : ℕ) (hq : ‖q‖≤2)
    (hA : 0≤A) (hL : 0≤L) (hR : (R:ℝ)+1≤A*L) :
    asymmetricLocalizationBound d q z B R ri rj ≤
      localizationFeedbackConstant d B A*L*
        (Real.sqrt (spectralScale z)*‖q-semicircleRoot z‖+‖q-semicircleRoot z‖^2)+
      localizationTailConstant d*physicalTransfer d z^(ri+rj) := by
  let C := finiteExtraReferenceConstant d
  let C0 := coreConvolutionConstant (finiteOmega d+1)
  let F := Real.sqrt (spectralScale z)*‖q-semicircleRoot z‖+‖q-semicircleRoot z‖^2
  have hC : 0≤C := (by norm_num : (0:ℝ)≤1).trans (finiteExtraReferenceConstant_ge_one d hd)
  have hC0 : 0≤C0 := coreConvolutionConstant_nonnegative _
  have hF : 0≤F := by dsimp only [F]; positivity
  have hk : 0<(d:ℝ)-1 := by have hh : (3:ℝ)≤d := Nat.cast_le.mpr hd; linarith
  have hM : localizationExceptionalMass d q≤localizationExceptionalMass d (2:ℂ) := by
    unfold localizationExceptionalMass
    norm_num only [Complex.norm_ofNat]
    apply div_le_div_of_nonneg_right _ hk.le
    exact add_le_add_left (mul_le_mul_of_nonneg_right hq (by positivity)) _
  have hcoef : 8*C^2*localizationExceptionalMass d q+
      4*C^2*‖q‖*(((finiteOmega d:ℝ)+1)/((d:ℝ)-1))+2*C ≤ localizationTailConstant d := by
    have hh1 := mul_le_mul_of_nonneg_left hM (show 0≤8*C^2 by positivity)
    have hh2 := mul_le_mul_of_nonneg_right hq
      (show 0≤4*C^2*(((finiteOmega d:ℝ)+1)/((d:ℝ)-1)) by positivity)
    dsimp only [localizationTailConstant]
    nlinarith only [hh1,hh2]
  have hfeedback : ordinaryFeedbackBudget z q B R ≤2*A*L*(Real.sqrt (B+2)+128)*F := by
    have hbase : Real.sqrt (B+2)*Real.sqrt (spectralScale z)*‖q-semicircleRoot z‖+
        128*‖q-semicircleRoot z‖^2 ≤(Real.sqrt (B+2)+128)*F := by
      dsimp only [F]
      nlinarith [mul_nonneg (Real.sqrt_nonneg (B+2)) (sq_nonneg ‖q-semicircleRoot z‖),
        mul_nonneg (Real.sqrt_nonneg (spectralScale z)) (norm_nonneg (q-semicircleRoot z))]
    have hlen : (((2*R:ℕ)+1):ℝ)≤2*A*L := by push_cast; nlinarith only [hR]
    unfold ordinaryFeedbackBudget
    exact (mul_le_mul hlen hbase (by positivity) (by positivity)).trans_eq (by ring)
  have hfirst := mul_le_mul_of_nonneg_left hfeedback (show 0≤32*C^2*C0 by positivity)
  have hlast := mul_le_mul_of_nonneg_right hcoef (pow_nonneg (physicalTransfer_pos d hd z).le (ri+rj))
  dsimp only [asymmetricLocalizationBound,localizationFeedbackConstant]
  convert add_le_add hfirst hlast using 1
  dsimp only [C,C0,F]
  ring

variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

theorem componentwise_weak_restriction_localization_asymmetric (g : DeficientGraph V d) (hd : 3≤d)
    (hbudget : g.ComponentFiniteReferenceBudget) (S : Set V)
    (q z : ℂ) (hz : 0<z.im) (hq : 0 ≤ q.im) (B : ℝ) (hzB : ‖z‖≤B)
    (ε L A : ℝ) (hε : 0≤ε) (hεOne : ε≤1) (hL : 1≤L) (hA : 0≤A) (hcap : ε*L^4≤1)
    (hprior : ‖q-semicircleRoot z‖≤scalarScale (spectralScale z) ε)
    (R Rs : ℕ) (hR : ∀ a b,g.graph.dist a b≤R) (hRs : ∀ a b,(g.restrict S).graph.dist a b≤Rs)
    (hRlog : (R:ℝ)+1≤A*L) (hRslog : (Rs:ℝ)+1≤A*L)
    (hlarge : localizationBudgetConstant d B A≤L)
    (i j : S) (ri rj : ℕ)
    (hI : graphBallVertices g.graph i.val ri⊆S) (hJ : graphBallVertices g.graph j.val rj⊆S) :
    ‖g.extensionGreen q z i.val j.val-(g.restrict S).extensionGreen q z i j‖≤
      2*localizationFeedbackConstant d B A*L*ε+
        localizationTailConstant d*physicalTransfer d z^(ri+rj) := by
  obtain ⟨sG,sS,sO,sC,sOrd⟩:=weak_localization_feedback_budgets d hd z q hz B ε L A
    hε hL hA hcap hprior R Rs hRlog hRslog hlarge
  have hlocal:=g.componentwise_restriction_localization_asymmetric hd hbudget S q z hz hq B hzB
    R Rs hR hRs sG sS sO sC sOrd i j ri rj hI hJ
  have hbound:=asymmetricLocalizationBound_feedback d hd z q B L A R ri rj
    (weak_boundary_norm_le_two z q hz ε hε hεOne hprior) hA (by linarith) hRlog
  have hlin:Real.sqrt (spectralScale z)*‖q-semicircleRoot z‖≤ε :=
    (mul_le_mul_of_nonneg_left hprior (Real.sqrt_nonneg (spectralScale z))).trans
      (scalarScale_sqrt_mul_le (spectralScale_pos hz) hε)
  have hquad:‖q-semicircleRoot z‖^2≤ε :=
    (pow_le_pow_left₀ (norm_nonneg _) hprior 2).trans (scalarScale_sq_le (spectralScale_pos hz) hε)
  have hK : 0≤localizationFeedbackConstant d B A*L := by
    have hC0:=coreConvolutionConstant_nonnegative (finiteOmega d+1)
    unfold localizationFeedbackConstant
    positivity
  exact (hlocal.trans hbound).trans (by
    have hh:=mul_le_mul_of_nonneg_left (add_le_add hlin hquad) hK
    nlinarith only [hh])

end DeficientGraph
end LocalLaw
