import LocalLaw.ActualOmittedKeptLeafDecay
import LocalLaw.OmittedRestoredUniformDecay

/-! # Uniform source-scale target to kept-leaf decay -/

noncomputable section
set_option maxHeartbeats 3500000
namespace LocalLaw
local instance omittedKeptLeafUniformDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ}{ι : Type}[Fintype ι]

def OmittedKeptLeafDecayControlled (g : RegularGraph N d)(hd : 3≤d)(T : Set (Fin N))
    (labels : ι ≃ BoundaryOrientedEdge g.graph T)(samples : LocalSamplingFiber g.graph T)
    (selector : ℕ)(S : Set (Tᶜ : Set (Fin N)))(q z : ℂ)(B C1 A L ε : ℝ) : Prop :=
  let s := g.admissibleState T labels samples
  letI : DecidableEq (s.OmittedCore selector S) := fun a b => Classical.propDecidable (a=b)
  let J := s.OmittedOrdinaryLeaves selector S ⊕ s.OmittedExtraLeaves selector S
  letI : DecidableEq J := fun a b => Classical.propDecidable (a=b)
  ∀x:s.OmittedCore selector S,∀l:J,∀h:ℕ,
    (h:ℕ∞)≤(g.omittedCommonModel T labels samples selector S).graph.edist x
      (s.omittedAllMate selector S (s.omittedKeptEmbedding selector S l)) →
    ‖(g.omittedKeptCompletion (by omega:1≤d) T labels samples selector S).extensionGreen q z (.inl x) (.inr l)‖≤
      omittedRestoredSpatialConstant d B A*L*physicalTransfer d z^h+
        omittedRestoredErrorConstant d B C1 A*L*ε

theorem actual_omitted_kept_leaf_uniform_decay (g : RegularGraph N d)(hd : 3≤d)(T : Set (Fin N))
    (labels : ι ≃ BoundaryOrientedEdge g.graph T)(samples : LocalSamplingFiber g.graph T)
    (selector r : ℕ)(S : Set (Tᶜ : Set (Fin N)))(q z : ℂ)(B C1 A L ε : ℝ)
    (hz : 0<z.im)(hq : 0≤q.im)(hp : rationalTreeReference (d-1) q≠0)
    (hpInv : ‖(rationalTreeReference (d-1) q)⁻¹‖≤2*|B|+3)
    (hL : 1≤L)(hε : 0≤ε)(_hA : 0≤A)
    (hinputs : g.OmittedLeafInputs hd T labels samples selector r S q z B C1 A L ε) :
    g.OmittedKeptLeafDecayControlled hd T labels samples selector S q z B C1 A L ε := by
  dsimp only [OmittedKeptLeafDecayControlled]
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
  have hr := g.actual_omitted_kept_leaf_decay hd T labels samples selector r S q z B C1 A L ε
    hz hq hp hLp hε hinputs x y h hfar
  apply hr.trans
  have hsp := mul_le_mul_of_nonneg_right hcoef (pow_nonneg (physicalTransfer_pos d hd z).le h)
  calc
    _ ≤ ((C+P*C^2*K*A)*L*physicalTransfer d z^h+(2*P^2*D*W^2)*L*ε)+
        omittedNormalizationConstant d B C1*L*ε := add_le_add (add_le_add hsp hErr) hNscale
    _ = _ := by dsimp only [omittedRestoredSpatialConstant,omittedRestoredErrorConstant,C,P,K,D,W];ring

end RegularGraph
end LocalLaw
