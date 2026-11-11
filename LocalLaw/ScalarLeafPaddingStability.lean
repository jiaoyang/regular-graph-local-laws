import LocalLaw.ScalarLeafPadding

/-! # Scalar-diagonal stability survives common-index leaf padding -/

noncomputable section
namespace LocalLaw
local instance scalarLeafPaddingStabilityDecidable (p:Prop):Decidable p:=Classical.propDecidable p
variable {I:Type} [Fintype I] [DecidableEq I]

omit [Fintype I] in
theorem scalarLeafPadding_diagonal (E:Set I) (p:ℂ) :
    scalarLeafPadding E (Matrix.diagonal (fun _:E=>p)) p=Matrix.diagonal (fun _:I=>p) := by
  have hb:Matrix.fromBlocks (Matrix.diagonal (fun _:E=>p)) 0 0
      (Matrix.diagonal (fun _:(Eᶜ:Set I)=>p))=Matrix.diagonal (fun _:E⊕(Eᶜ:Set I)=>p):=by
    ext u v
    cases u <;> cases v <;>
      simp [Matrix.diagonal_apply,Sum.inl.injEq,Sum.inr.injEq]
  unfold scalarLeafPadding
  rw [hb,Matrix.submatrix_diagonal_equiv]
  rfl

omit [Fintype I] in
theorem scalarLeafPadding_difference_diagonal (E:Set I) (R:Matrix E E ℂ) (p:ℂ) :
    scalarLeafPadding E R p-Matrix.diagonal (fun _:I=>p)=
      scalarLeafPadding E (R-Matrix.diagonal (fun _:E=>p)) 0 := by
  rw [←scalarLeafPadding_diagonal E p]
  unfold scalarLeafPadding
  ext i j
  simp only [Matrix.submatrix_apply,Matrix.sub_apply]
  cases hi:(Equiv.Set.sumCompl E).symm i <;>
    cases hj:(Equiv.Set.sumCompl E).symm j <;> simp [Matrix.sub_apply,Matrix.diagonal_apply]

omit [Fintype I] in
theorem scalarLeafPadding_entry_error (E:Set I) (R:Matrix E E ℂ) (p:ℂ) (δ:ℝ) (hδ:0≤δ)
    (herr:∀i j:E,‖R i j-(if i=j then p else 0)‖≤δ) :
    ∀i j:I,‖scalarLeafPadding E R p i j-(if i=j then p else 0)‖≤δ := by
  intro i j
  change ‖(scalarLeafPadding E R p-Matrix.diagonal (fun _:I=>p)) i j‖≤δ
  rw [scalarLeafPadding_difference_diagonal]
  simp only [scalarLeafPadding,Matrix.submatrix_apply]
  cases hi:(Equiv.Set.sumCompl E).symm i with
  | inl a =>
    cases hj:(Equiv.Set.sumCompl E).symm j with
    | inl b => simpa only [Matrix.fromBlocks_apply₁₁,Matrix.sub_apply,Matrix.diagonal_apply] using herr a b
    | inr b => simpa only [Matrix.fromBlocks_apply₁₂,Matrix.zero_apply,norm_zero] using hδ
  | inr a =>
    cases hj:(Equiv.Set.sumCompl E).symm j with
    | inl b => simpa only [Matrix.fromBlocks_apply₂₁,Matrix.zero_apply,norm_zero] using hδ
    | inr b => simpa [Matrix.diagonal_apply] using hδ

theorem scalarLeafPadding_inverse_stability (E:Set I) (R:Matrix E E ℂ) (p:ℂ)
    (hR:IsUnit R) (hp:p≠0) (δ:ℝ) (hδ:0≤δ)
    (herr:∀i j:E,‖R i j-(if i=j then p else 0)‖≤δ)
    (hsmall:(Fintype.card E:ℝ)*‖p⁻¹‖*δ≤1/2) :
    ∀i j:I,‖(scalarLeafPadding E R p)⁻¹ i j-(if i=j then p⁻¹ else 0)‖≤2*‖p⁻¹‖^2*δ := by
  rw [(scalarLeafPadding_inverse E R p hR hp).2]
  exact scalarLeafPadding_entry_error E R⁻¹ p⁻¹ (2*‖p⁻¹‖^2*δ) (by positivity)
    (scalar_diagonal_inverse_stability R p hp hR δ hδ herr hsmall)

end LocalLaw
