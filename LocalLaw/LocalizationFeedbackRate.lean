import LocalLaw.ComponentWeakLocalization

/-!
# Keep the target feedback visible in finite pair localization

The finite localization formula is bounded before replacing its scalar
feedback by the weak error. This retains the improvement subsequently
obtained from strong scalar closure.
-/

noncomputable section
namespace LocalLaw
namespace DeficientGraph

def localizationFeedbackConstant (d : ℕ) (B A : ℝ) : ℝ :=
  64*A*(Real.sqrt (B+2)+128)*finiteExtraReferenceConstant d^2*coreConvolutionConstant (finiteOmega d+1)

def localizationTailConstant (d : ℕ) : ℝ :=
  let C := finiteExtraReferenceConstant d
  8*C^2*localizationExceptionalMass d (2:ℂ)+
    8*C^2*(((finiteOmega d:ℝ)+1)/((d:ℝ)-1))+2*C

theorem finitePairLocalizationBound_feedback (d : ℕ) (hd : 3≤d)
    (z q : ℂ) (B L A : ℝ) (R r : ℕ) (hq : ‖q‖≤2)
    (hA : 0≤A) (hL : 0≤L) (hR : (R:ℝ)+1≤A*L) :
    finitePairLocalizationBound d q z B R r ≤
      localizationFeedbackConstant d B A*L*
        (Real.sqrt (spectralScale z)*‖q-semicircleRoot z‖+‖q-semicircleRoot z‖^2)+
      localizationTailConstant d*physicalTransfer d z^(2*r) := by
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
  have hlast := mul_le_mul_of_nonneg_right hcoef (pow_nonneg (physicalTransfer_pos d hd z).le (2*r))
  dsimp only [finitePairLocalizationBound,localizationFeedbackConstant]
  convert add_le_add hfirst hlast using 1
  dsimp only [C,C0,F]
  ring

variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

/-- Actual finite localization with weak-prior feedback conditions derived,
but the sharper scalar feedback retained in the conclusion. -/
theorem componentwise_pair_localization_feedback (g : DeficientGraph V d) (hd : 3≤d)
    (hbudget : g.ComponentFiniteReferenceBudget) (q z : ℂ) (hz : 0<z.im) (hq : 0≤q.im)
    (B : ℝ) (hzB : ‖z‖≤B) (ε L A : ℝ) (hε : 0≤ε) (hεOne : ε≤1)
    (hL : 1≤L) (hA : 0≤A) (hcap : ε*L^4≤1)
    (hprior : ‖q-semicircleRoot z‖≤scalarScale (spectralScale z) ε)
    (R r : ℕ) (hR : ∀ i j,g.graph.dist i j≤R)
    (hRlog : (R:ℝ)+1≤A*L) (hrlog : ((4*r+1:ℕ)+1:ℝ)≤A*L)
    (hlarge : localizationBudgetConstant d B A≤L) (i j : V) :
    ‖g.extensionGreen q z i j-g.P r z q i j‖≤
      localizationFeedbackConstant d B A*L*
        (Real.sqrt (spectralScale z)*‖q-semicircleRoot z‖+‖q-semicircleRoot z‖^2)+
        localizationTailConstant d*physicalTransfer d z^(2*r) := by
  obtain ⟨sG,sS,sO,sC,sOrd⟩ := weak_localization_feedback_budgets d hd z q hz B ε L A hε hL hA
    hcap hprior R (4*r+1) hRlog hrlog hlarge
  exact (g.componentwise_pair_localization hd hbudget q z hz hq B hzB R r hR
    sG sS sO sC sOrd i j).trans
      (finitePairLocalizationBound_feedback d hd z q B L A R r
        (weak_boundary_norm_le_two z q hz ε hε hεOne hprior) hA (by linarith) hRlog)

end DeficientGraph
end LocalLaw
