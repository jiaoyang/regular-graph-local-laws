import LocalLaw.PartialLMaskStability
import LocalLaw.ActualPartialEndpointCaps
import LocalLaw.PartialVacuumSurgeryStability

/-! # Constant actual endpoint rows and columns from the L-mask surgery -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance partialLMaskRowsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {L : Type} [Fintype L] [DecidableEq L]

theorem partialLMask_surgery_rows (A B C Lmask : Set L) (A0 : Matrix A A ℂ) (q p α : ℂ)
    (hA : IsUnit A0) (hAsym : A0.IsSymm) (hq : q≠0) (hp : p≠0) (hrel : p⁻¹=q⁻¹-q*α^2)
    (P K δ : ℝ) (hP : 0≤P) (hK : 0≤K) (hδ : 0≤δ)
    (hqnorm : ‖q‖≤P) (hpnorm : ‖p‖≤P) (ha : ‖α*q‖≤1)
    (hrestored : IsUnit (A0-partialLMaskRestoration A Lmask q α))
    (hrows : ∀a,∑a',‖(A0-partialLMaskRestoration A Lmask q α)⁻¹ a a'‖≤K)
    (R T : Matrix (A⊕(B⊕C)) (A⊕(B⊕C)) ℂ)
    (hT : T+R*(partialTripleEdgeUpdate A B C α+partialLMaskCharge A B C Lmask q α)*T=R)
    (herror : ∀i j,‖(R-(partialTripleOldPrecision A B C A0 q p α)⁻¹) i j‖≤δ)
    (hsmall : (Fintype.card (A⊕(B⊕C)):ℝ)*
      (1+(P+2*K)*(2*‖α‖+‖q‖*‖α‖^2))*(2*‖α‖+‖q‖*‖α‖^2)*δ≤1/2)
    (hmass : (Fintype.card (A⊕(B⊕C)):ℝ)*
      (2*(1+(P+2*K)*(2*‖α‖+‖q‖*‖α‖^2))^2*δ)≤1) :
    (∀i,∑j,‖T i j‖≤P+2*K+1) ∧ (∀j,∑i,‖T i j‖≤P+2*K+1) := by
  let Q:=(partialLMaskNewPrecision A B C Lmask A0 q p α)⁻¹
  let σ:=2*(1+(P+2*K)*(2*‖α‖+‖q‖*‖α‖^2))^2*δ
  have hQ:=partialLMaskNewPrecision_inverse_caps A B C Lmask A0 q p α hAsym hq hp P K hP hK
    hqnorm hpnorm ha hrestored hrows
  have he:=partialLMask_surgery_stability A B C Lmask A0 q p α hA hAsym hq hp hrel
    P K δ hP hK hδ hqnorm hpnorm ha hrestored hrows R T hT herror hsmall
  have herr : ∀i j,‖T i j-Q i j‖≤σ := he
  have hcol : ∀j,∑i,‖Q.transpose j i‖≤P+2*K := hQ.2.2
  refine ⟨fun i=>?_,fun j=>?_⟩
  · exact (matrix_row_sum_of_entry_error T Q (P+2*K) σ hQ.2.1 herr i).trans (add_le_add_left hmass _)
  · exact (matrix_row_sum_of_entry_error T.transpose Q.transpose (P+2*K) σ hcol (fun i j=>herr j i) j).trans
      (add_le_add_left hmass _)

end LocalLaw
