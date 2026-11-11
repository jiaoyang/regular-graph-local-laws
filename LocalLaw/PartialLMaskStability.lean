import LocalLaw.PartialLMaskSurgery
import LocalLaw.PartialVacuumSurgeryStability

/-! # Class-free endpoint stability against the actual L-mask benchmark -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance partialLMaskStabilityDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {L : Type} [Fintype L] [DecidableEq L]

theorem partialLMask_surgery_stability (A B C Lmask : Set L) (A0 : Matrix A A ℂ) (q p α : ℂ)
    (hA : IsUnit A0) (hAsym : A0.IsSymm) (hq : q≠0) (hp : p≠0) (hrel : p⁻¹=q⁻¹-q*α^2)
    (P K δ : ℝ) (hP : 0≤P) (hK : 0≤K) (hδ : 0≤δ)
    (hqnorm : ‖q‖≤P) (hpnorm : ‖p‖≤P) (ha : ‖α*q‖≤1)
    (hrestored : IsUnit (A0-partialLMaskRestoration A Lmask q α))
    (hrows : ∀a,∑a',‖(A0-partialLMaskRestoration A Lmask q α)⁻¹ a a'‖≤K)
    (R T : Matrix (A⊕(B⊕C)) (A⊕(B⊕C)) ℂ)
    (hT : T+R*(partialTripleEdgeUpdate A B C α+partialLMaskCharge A B C Lmask q α)*T=R)
    (herror : ∀i j,‖(R-(partialTripleOldPrecision A B C A0 q p α)⁻¹) i j‖≤δ)
    (hsmall : (Fintype.card (A⊕(B⊕C)):ℝ)*
      (1+(P+2*K)*(2*‖α‖+‖q‖*‖α‖^2))*(2*‖α‖+‖q‖*‖α‖^2)*δ≤1/2) :
    ∀i j,‖(T-(partialLMaskNewPrecision A B C Lmask A0 q p α)⁻¹) i j‖≤
      2*(1+(P+2*K)*(2*‖α‖+‖q‖*‖α‖^2))^2*δ := by
  let Old:=partialTripleOldPrecision A B C A0 q p α
  let New:=partialLMaskNewPrecision A B C Lmask A0 q p α
  let W:=partialTripleEdgeUpdate A B C α+partialLMaskCharge A B C Lmask q α
  have hOld : IsUnit Old := (partialTripleOldPrecision_inverse A B C A0 q p α hA hq hp hrel).1
  have hNew:=partialLMaskNewPrecision_inverse_caps A B C Lmask A0 q p α hAsym hq hp P K hP hK
    hqnorm hpnorm ha hrestored hrows
  have hW : New-Old=W := by
    dsimp only [New,Old,W]
    rw [partialLMask_precision_update A B C Lmask A0 q p α hrel]
    abel
  have hQ:=inverse_update_of_difference Old New W hOld hNew.1 hW
  have hMass:=partialLMaskCoupling_mass A B C Lmask q α
  exact surgery_entry_stability R T Old⁻¹ New⁻¹ W hT hQ (P+2*K)
    (2*‖α‖+‖q‖*‖α‖^2) δ (by positivity) (by positivity) hδ
    hNew.2.1 hNew.2.2 hMass.1 hMass.2 herror hsmall

end LocalLaw
