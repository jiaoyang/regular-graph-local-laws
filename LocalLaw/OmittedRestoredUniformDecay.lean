import LocalLaw.ActualOmittedRestoredDecay

/-! # Fixed-constant logarithmic decay for the genuine switched deleted core -/

noncomputable section
set_option maxHeartbeats 3500000
namespace LocalLaw
local instance omittedRestoredUniformDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def omittedRestoredSpatialConstant (d : ℕ)(B A : ℝ) : ℝ :=
  2*finiteExtraReferenceConstant d+(2*|B|+3)*(2*finiteExtraReferenceConstant d)^2*
    coreConvolutionConstant (finiteOmega d+1)*A

def omittedRestoredErrorConstant (d : ℕ)(B C1 A : ℝ) : ℝ :=
  2*(2*|B|+3)^2*(|(treePatchWeakConstant d B A+2*finiteExtraReferenceConstant d)*C1^2|+1)*
    (4*finiteExtraReferenceConstant d)^2+omittedNormalizationConstant d B C1

namespace RegularGraph
variable {N d : ℕ}{ι : Type}[Fintype ι]

def OmittedRestoredDecayControlled (g : RegularGraph N d)(T : Set (Fin N))
    (labels : ι ≃ BoundaryOrientedEdge g.graph T)(samples : LocalSamplingFiber g.graph T)
    (selector : ℕ)(S : Set (Tᶜ : Set (Fin N)))(q z : ℂ)(B C1 A L ε : ℝ) : Prop :=
  let s := g.admissibleState T labels samples
  letI : DecidableEq (s.OmittedCore selector S) := fun a b => Classical.propDecidable (a=b)
  ∀x y:s.OmittedCore selector S,∀h:ℕ,
    (h:ℕ∞)≤(g.omittedCommonModel T labels samples selector S).graph.edist x y →
    ‖(g.omittedKeptRestoredModel T labels samples selector S).extensionGreen q z x y‖≤
      omittedRestoredSpatialConstant d B A*L*physicalTransfer d z^h+
        omittedRestoredErrorConstant d B C1 A*L*ε

theorem actual_omitted_restored_uniform_decay (g : RegularGraph N d)(hd : 3≤d)(T : Set (Fin N))
    (labels : ι ≃ BoundaryOrientedEdge g.graph T)(samples : LocalSamplingFiber g.graph T)
    (selector r : ℕ)(S : Set (Tᶜ : Set (Fin N)))(q z : ℂ)(B C1 A L ε : ℝ)
    (hz : 0<z.im)(hq : 0≤q.im)(hp : rationalTreeReference (d-1) q≠0)
    (hpInv : ‖(rationalTreeReference (d-1) q)⁻¹‖≤2*|B|+3)
    (hL : 1≤L)(hε : 0≤ε)(_hA : 0≤A)
    (hinputs : g.OmittedLeafInputs hd T labels samples selector r S q z B C1 A L ε)
    (hcontrol : g.OmittedKeptControlled hd T labels samples selector S q z B C1 ε) :
    g.OmittedRestoredDecayControlled T labels samples selector S q z B C1 A L ε := by
  dsimp only [OmittedRestoredDecayControlled]
  intro x y h hfar
  let R := hereditaryReferenceRadius d (hereditaryReferenceRadius d (augmentedObservationDiameter d r))+2
  let p := rationalTreeReference (d-1) q
  let C := 2*finiteExtraReferenceConstant d
  let P := 2*|B|+3
  let D := |(treePatchWeakConstant d B A+2*finiteExtraReferenceConstant d)*C1^2|+1
  let W := 4*finiteExtraReferenceConstant d
  let K := coreConvolutionConstant (finiteOmega d+1)
  have hCe : 0≤finiteExtraReferenceConstant d := by linarith [finiteExtraReferenceConstant_ge_one d hd]
  have hC : 0≤C := by dsimp only [C];positivity
  have hP : 0≤P := by dsimp only [P];positivity
  have hD : 0≤D := by dsimp only [D];positivity
  have hW : 0≤W := by dsimp only [W];positivity
  have hK : 0≤K := coreConvolutionConstant_nonnegative _
  have hLp : 0≤L := by linarith
  have hR : 0≤(R:ℝ)+1 := by positivity
  have hlog : (R:ℝ)+1≤A*L := hinputs.2.2.1
  have hcoef : C+‖p⁻¹‖*C^2*K*((R:ℝ)+1)≤(C+P*C^2*K*A)*L := by
    calc
      _ ≤ C+P*C^2*K*(A*L) := by gcongr
      _ ≤ C*L+P*C^2*K*(A*L) := by nlinarith only [mul_le_mul_of_nonneg_left hL hC]
      _ = _ := by ring
  have hErr : 2*‖p⁻¹‖^2*(D*L*ε)*W^2≤(2*P^2*D*W^2)*L*ε := by
    calc
      _ ≤ 2*P^2*(D*L*ε)*W^2 := by gcongr
      _ = _ := by ring
  have hN : 0≤omittedNormalizationConstant d B C1 := by
    unfold omittedNormalizationConstant omittedNormalizationCoefficient omittedKeptRowConstant
    positivity
  have hNscale : omittedNormalizationConstant d B C1*ε≤omittedNormalizationConstant d B C1*L*ε := by
    nlinarith only [mul_le_mul_of_nonneg_left hL (mul_nonneg hN hε)]
  have hr := g.actual_omitted_restored_decay hd T labels samples selector r S q z B C1 A L ε
    hz hq hp hLp hε hinputs hcontrol x y h hfar
  apply hr.trans
  have hsp := mul_le_mul_of_nonneg_right hcoef (pow_nonneg (physicalTransfer_pos d hd z).le h)
  calc
    _ ≤ ((C+P*C^2*K*A)*L*physicalTransfer d z^h+(2*P^2*D*W^2)*L*ε)+
        omittedNormalizationConstant d B C1*L*ε := add_le_add (add_le_add hsp hErr) hNscale
    _ = _ := by dsimp only [omittedRestoredSpatialConstant,omittedRestoredErrorConstant,C,P,K,D,W];ring

end RegularGraph
end LocalLaw
