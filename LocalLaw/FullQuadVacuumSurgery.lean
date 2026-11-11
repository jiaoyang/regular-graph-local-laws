import LocalLaw.FullQuadVacuumRows
import LocalLaw.PartialVacuumSurgeryStability

/-! # Finite-rank stability for the full partial-switching benchmark -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance fullQuadVacuumSurgeryDecidable (p:Prop):Decidable p:=Classical.propDecidable p
variable {K L:Type} [Fintype K] [Fintype L] [DecidableEq K] [DecidableEq L]

theorem fullQuadOldPrecision_inverse (B C:Set L) (A₀:Matrix K K ℂ) (q p α:ℂ)
    (hA:IsUnit A₀) (hq:q≠0) (hp:p≠0) (hrel:p⁻¹=q⁻¹-q*α^2) :
    IsUnit (fullQuadOldPrecision B C A₀ q p α)∧
      (fullQuadOldPrecision B C A₀ q p α)⁻¹=
        Matrix.fromBlocks A₀⁻¹ 0 0 (partialSampleCovariance B C q p α) := by
  have hs:=partialSamplePrecision_inverse B C q p α hq hp hrel
  have hb:=blockDiagonal_inverse A₀ (partialSamplePrecision B C q p α) hA hs.1
  exact ⟨hb.1,by simpa only [fullQuadOldPrecision,hs.2] using hb.2⟩

theorem fullQuadVacuum_surgery_stability (inner outer:L→Option K) (B C:Set L)
    (A₀:Matrix K K ℂ) (q p α:ℂ) (hA:IsUnit A₀) (hAsym:A₀.IsSymm)
    (hq:q≠0) (hp:p≠0) (hrel:p⁻¹=q⁻¹-q*α^2)
    (P R a w δ:ℝ) (hP:0≤P) (hR:0≤R) (ha:0≤a) (hw:0≤w) (hδ:0≤δ)
    (hqnorm:‖q‖≤P) (hpnorm:‖p‖≤P) (hαq:‖α*q‖≤1)
    (hmultiplicity:∀k,(Nat.card {j:B⊕C//fullQuadLeafMate inner outer B C j=some k}:ℝ)≤a)
    (hcut:IsUnit (A₀-fullQuadRetainedEdges inner outer α-
      Matrix.diagonal (fun k=>q*α^2*fullQuadRetainedDegree inner outer k)))
    (hcutRows:∀k,∑k',‖(A₀-fullQuadRetainedEdges inner outer α-
      Matrix.diagonal (fun k=>q*α^2*fullQuadRetainedDegree inner outer k))⁻¹ k k'‖≤R)
    (Old New:Matrix (K⊕(B⊕C)) (K⊕(B⊕C)) ℂ)
    (hUpdate:New+Old*fullQuadSurgeryCoupling inner outer B C q α*New=Old)
    (hWrow:∀i,∑j,‖fullQuadSurgeryCoupling inner outer B C q α i j‖≤w)
    (hWcol:∀j,∑i,‖fullQuadSurgeryCoupling inner outer B C q α i j‖≤w)
    (herror:∀i j,‖(Old-(fullQuadOldPrecision B C A₀ q p α)⁻¹) i j‖≤δ)
    (hsmall:(Fintype.card (K⊕(B⊕C)):ℝ)*(1+(P+(1+a)*R)*w)*w*δ≤1/2) :
    ∀i j,‖(New-(fullQuadVacuumPrecision inner outer B C A₀ q p α)⁻¹) i j‖≤
      2*(1+(P+(1+a)*R)*w)^2*δ := by
  let A:=fullQuadOldPrecision B C A₀ q p α
  let D:=fullQuadVacuumPrecision inner outer B C A₀ q p α
  let W:=fullQuadSurgeryCoupling inner outer B C q α
  have hOldUnit:IsUnit A:=(fullQuadOldPrecision_inverse B C A₀ q p α hA hq hp hrel).1
  have hNewUnit:IsUnit D:=(fullQuadVacuum_schur inner outer B C A₀ q p α hq hp hcut).1
  have hDiff:D-A=W:=by
    dsimp only [A,D,W]
    rw [fullQuadVacuum_precision_update inner outer B C A₀ q p α hrel]
    abel
  have hQ:=inverse_update_of_difference A D W hOldUnit hNewUnit hDiff
  have hRows:=fullQuadVacuum_inverse_rows inner outer B C A₀ q p α hq hp P R a hP hR ha
    hqnorm hpnorm hαq hmultiplicity hcut hcutRows
  have hCols:=fullQuadVacuum_inverse_columns inner outer B C A₀ q p α hAsym hq hp P R a hP hR ha
    hqnorm hpnorm hαq hmultiplicity hcut hcutRows
  exact surgery_entry_stability Old New A⁻¹ D⁻¹ W hUpdate hQ (P+(1+a)*R) w δ
    (by positivity) hw hδ hRows hCols hWrow hWcol herror hsmall

end LocalLaw
