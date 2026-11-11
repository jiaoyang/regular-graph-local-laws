import LocalLaw.LeafCompletionAnalytic

/-! # Fixed constants for the leaf-completion localization error -/

noncomputable section
namespace LocalLaw

def leafCompletionMainCoefficient (d : ℕ) (B A C1 : ℝ) : ℝ :=
  let P:=2*|B|+3
  let W:=4*finiteExtraReferenceConstant d
  2*|DeficientGraph.localizationFeedbackConstant d B A| * C1^2*(1+2*P*W)+
    4*P^2*leafCovarianceCoefficient d B A C1*W^2

def leafCompletionTailCoefficient (d : ℕ) (B : ℝ) : ℝ :=
  let C:=2*finiteExtraReferenceConstant d
  let v:=|DeficientGraph.localizationTailConstant d|
  v+(2*|B|+3)*(2*v*C+C^2)

theorem leafCompletionMainCoefficient_nonnegative (d : ℕ) (hd : 3≤d) (B A C1 : ℝ) :
    0≤leafCompletionMainCoefficient d B A C1 := by
  have hC:=finiteExtraReferenceConstant_ge_one d hd
  have hδ:=leafCovarianceCoefficient_nonnegative d B A C1
  unfold leafCompletionMainCoefficient
  positivity

theorem leafCompletionTailCoefficient_nonnegative (d : ℕ) (hd : 3≤d) (B : ℝ) :
    0≤leafCompletionTailCoefficient d B := by
  have hC:=finiteExtraReferenceConstant_ge_one d hd
  unfold leafCompletionTailCoefficient
  positivity

theorem leaf_completion_error_coarsening (d : ℕ) (hd : 3≤d) (B A C1 L ε n t : ℝ)
    (hL : 0≤L) (hε : 0≤ε) (hn : 0≤n) (ht : 0≤t) (p : ℂ) (hp : ‖p⁻¹‖≤2*|B|+3) :
    let u:=2*DeficientGraph.localizationFeedbackConstant d B A*L*(C1^2*ε)
    let v:=DeficientGraph.localizationTailConstant d
    let C:=2*finiteExtraReferenceConstant d
    let W:=4*finiteExtraReferenceConstant d
    u+v*t+‖p⁻¹‖*(2*u*W+(2*v*C+C^2)*n*t)+
      4*‖p⁻¹‖^2*(leafCovarianceCoefficient d B A C1*L*ε)*W^2≤
      leafCompletionMainCoefficient d B A C1*L*ε+leafCompletionTailCoefficient d B*(n+1)*t := by
  dsimp only
  let P:=2*|B|+3
  let C:=2*finiteExtraReferenceConstant d
  let W:=4*finiteExtraReferenceConstant d
  let κ:=2*|DeficientGraph.localizationFeedbackConstant d B A| * C1^2
  let v:=|DeficientGraph.localizationTailConstant d|
  let u:=2*DeficientGraph.localizationFeedbackConstant d B A*L*(C1^2*ε)
  let δ:=leafCovarianceCoefficient d B A C1*L*ε
  have hC0 : 0≤C := by dsimp only [C]; linarith [finiteExtraReferenceConstant_ge_one d hd]
  have hW0 : 0≤W := by dsimp only [W]; linarith [finiteExtraReferenceConstant_ge_one d hd]
  have hP0 : 0≤P := by dsimp only [P]; positivity
  have hκ0 : 0≤κ := by dsimp only [κ]; positivity
  have hv0 : 0≤v := abs_nonneg _
  have hδ0 : 0≤δ := mul_nonneg (mul_nonneg (leafCovarianceCoefficient_nonnegative d B A C1) hL) hε
  have hu : u≤κ*L*ε := by
    have hh:=mul_le_mul_of_nonneg_right (le_abs_self (DeficientGraph.localizationFeedbackConstant d B A))
      (show 0≤2*C1^2*L*ε by positivity)
    convert hh using 1 <;> dsimp only [u,κ] <;> ring
  have hv : DeficientGraph.localizationTailConstant d≤v := le_abs_self _
  have hfirst : u+DeficientGraph.localizationTailConstant d*t+
      ‖p⁻¹‖*(2*u*W+(2*DeficientGraph.localizationTailConstant d*C+C^2)*n*t)+4*‖p⁻¹‖^2*δ*W^2≤
      κ*L*ε+v*t+‖p⁻¹‖*(2*(κ*L*ε)*W+(2*v*C+C^2)*n*t)+4*‖p⁻¹‖^2*δ*W^2 := by
    gcongr
  have hsecond : κ*L*ε+v*t+‖p⁻¹‖*(2*(κ*L*ε)*W+(2*v*C+C^2)*n*t)+4*‖p⁻¹‖^2*δ*W^2≤
      κ*L*ε+v*t+P*(2*(κ*L*ε)*W+(2*v*C+C^2)*n*t)+4*P^2*δ*W^2 := by
    gcongr
  have htail : v+P*(2*v*C+C^2)*n≤(v+P*(2*v*C+C^2))*(n+1) := by
    nlinarith [mul_nonneg hv0 hn,mul_nonneg hP0 (show 0≤2*v*C+C^2 by positivity)]
  calc
    _≤κ*L*ε+v*t+P*(2*(κ*L*ε)*W+(2*v*C+C^2)*n*t)+4*P^2*δ*W^2 := hfirst.trans hsecond
    _=(κ*(1+2*P*W)+4*P^2*leafCovarianceCoefficient d B A C1*W^2)*L*ε+
        (v+P*(2*v*C+C^2)*n)*t := by dsimp only [δ]; ring
    _≤(κ*(1+2*P*W)+4*P^2*leafCovarianceCoefficient d B A C1*W^2)*L*ε+
        ((v+P*(2*v*C+C^2))*(n+1))*t := add_le_add_left (mul_le_mul_of_nonneg_right htail ht) _
    _=_ := by rfl

end LocalLaw
