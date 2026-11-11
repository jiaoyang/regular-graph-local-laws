import LocalLaw.ExceptionalSelfEnergySupport
import LocalLaw.CutComponentDiameter

/-!
# Finite-model localization from actual graph and inverse data

The ordinary component residual, exceptional coupling support/mass, model
reference class, and genuine Schur inverses are all proved earlier. This
assembly retains only explicit intrinsic diameter and finite numerical
feedback budgets, rather than assuming a localization estimate.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance finiteLocalizationDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace DeficientGraph
variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

def localizationExceptionalMass (d : ℕ) (q : ℂ) : ℝ :=
  (5 * finiteExtraReferenceConstant d * (2 * (finiteOmega d : ℝ)) ^ 2 +
    ‖q‖ * (2 * (finiteOmega d : ℝ))) / ((d : ℝ) - 1)

theorem exterior_zero_schur_localization (g : DeficientGraph V d) (hd : 3 ≤ d)
    (S : Set V) (hzero : ∀ v ∉ S, g.deficit v = 0)
    (hG : g.graph.Connected) (hS : (g.graph.induce S).Connected) (hbudget : g.FiniteReferenceBudget)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) (Bcap : ℝ) (hBcap : ‖z‖ ≤ Bcap)
    (R Rs : ℕ) (hR : ∀ a b, g.graph.dist a b ≤ R)
    (hRs : ∀ a b, (g.graph.induce S).dist a b ≤ Rs)
    (smallG : ‖q - semicircleRoot z‖ * finiteExtraReferenceConstant d *
      coreConvolutionConstant (finiteOmega d + 1) * ((R : ℝ) + 1) ≤ 1 / 2)
    (smallS : ‖q - semicircleRoot z‖ * finiteExtraReferenceConstant d *
      coreConvolutionConstant (finiteOmega d + 1) * ((Rs : ℝ) + 1) ≤ 1 / 2)
    (smallOutside : ‖q - semicircleRoot z‖ * finiteExtraReferenceConstant d *
      coreConvolutionConstant (finiteOmega d + 1) * (((finiteOmega d + 1) * (2 * R + 1) : ℕ) + 1 : ℝ) ≤ 1 / 2)
    (smallCavity : ‖q - semicircleRoot z‖ * 3 * (3 / 2 : ℝ) * ((2 * R : ℕ) + 1 : ℝ) ≤ 1 / 2)
    (smallOrdinary : ordinaryFeedbackBudget z q Bcap R * (2 * finiteExtraReferenceConstant d) *
      coreConvolutionConstant (finiteOmega d + 1) * ((Rs : ℝ) + 1) ≤ 1 / 2)
    (i j : S) (r : ℕ) (hcontain : pairBallVertices g.graph i.val j.val r ⊆ S) :
    ‖g.extensionGreen q z i.val j.val - (g.restrict S).extensionGreen q z i j‖ ≤
      32 * finiteExtraReferenceConstant d ^ 2 * coreConvolutionConstant (finiteOmega d + 1) *
        ordinaryFeedbackBudget z q Bcap R +
      8 * finiteExtraReferenceConstant d ^ 2 * localizationExceptionalMass d q * physicalTransfer d z ^ (2 * r) := by
  let model := g.restrict S
  let A := model.extensionMatrix q z
  let E := g.ordinarySelfEnergyError S q z
  let W := g.exceptionalSelfEnergy S q z
  let F := (g.extensionGreen q z).submatrix (Subtype.val : S → V) (Subtype.val : S → V)
  let K := model.referenceDecay z
  let B := model.referenceCompanion z
  let C := finiteExtraReferenceConstant d
  let Cbar := 2 * C
  let C₀ := coreConvolutionConstant (finiteOmega d + 1)
  let τ := ordinaryFeedbackBudget z q Bcap R
  let ρ := physicalTransfer d z ^ r
  let M := localizationExceptionalMass d q
  have hC : 0 ≤ C := le_trans (by norm_num) (finiteExtraReferenceConstant_ge_one d hd)
  have hCbar : 0 ≤ Cbar := by positivity
  have hC₀ : 0 ≤ C₀ := coreConvolutionConstant_nonnegative _
  have hτ : 0 ≤ τ := ordinaryFeedbackBudget_nonnegative _ _ _ _
  have ht : 0 ≤ physicalTransfer d z := (physicalTransfer_pos d hd z).le
  have htone : physicalTransfer d z ≤ 1 := by have hh := physicalTransfer_sq_le_half d hd z; nlinarith
  have hρ : 0 ≤ ρ := pow_nonneg ht _
  have hSne : S.Nonempty := by obtain ⟨v⟩ := hS.nonempty; exact ⟨v.val, v.property⟩
  have hbudgetS := g.restrict_finiteReferenceBudget S hG hS hbudget
  have hexS : graphExcess model.graph ≤ finiteOmega d + 1 := by
    dsimp only [model]
    have hh := hbudgetS.complexity_le
    omega
  have hA : IsUnit A := model.extensionMatrix_isUnit hd q z hz hq
  have hD : IsUnit ((g.extensionMatrix q z).submatrix
      (Subtype.val : (Sᶜ : Set V) → V) (Subtype.val : (Sᶜ : Set V) → V)) := by
    rw [← g.extensionMatrix_delete S q z]
    exact (g.delete S).extensionMatrix_isUnit hd q z hz hq
  have hF : IsUnit F := retained_principal_inverse_isUnit S (g.extensionMatrix q z)
    (g.extensionMatrix_isUnit hd q z hz hq) hD
  letI : Invertible F := Classical.choice hF.nonempty_invertible
  have hSchur : F⁻¹ = A - Matrix.diagonal E - W :=
    g.retained_inverse_ordinary_exceptional_split hd S hG hSne q z hz hq
  have hfull : IsUnit (A - Matrix.diagonal E - W) := by
    rw [← hSchur]
    exact isUnit_of_invertible _
  have hfinal : (A - Matrix.diagonal E - W)⁻¹ = F := by
    rw [← hSchur, Matrix.inv_inv_of_invertible]
  have hordinary : IsUnit (A - Matrix.diagonal E) := g.ordinary_self_energy_matrix_isUnit hd S q z hz hq
  have hE : ∀ u, ‖E u‖ ≤ τ * model.boundaryCoefficient u :=
    g.ordinarySelfEnergyError_model_bound hd S hzero hG hSne q z hz hq Bcap hBcap R hR smallCavity
  have href : ∀ a b, ‖A⁻¹ a b‖ ≤ Cbar * K a b :=
    model.finite_class_kernel_bound hd hS hbudgetS z q hz hq Rs hRs smallS
  have hconv : ∀ a b, (∑ u, model.boundaryCoefficient u * K a u * K u b) ≤ C₀ * B a b :=
    model.referenceDecay_convolution hd hS (finiteOmega d + 1) hexS z
  have hnear : ∀ a ∈ exceptionalPorts g.graph S, K i a ≤ ρ := by
    intro a ha
    have hfar := (exceptional_port_distance g.graph hG S i.val j.val r hcontain a ha).1
    have hdist := hfar.trans (induced_distance_lower g.graph S hS i a)
    exact pow_le_pow_of_le_one ht htone hdist
  have hcol : ∀ b ∈ exceptionalPorts g.graph S, ‖(A - Matrix.diagonal E - W)⁻¹ b j‖ ≤ Cbar * ρ := by
    intro b hb
    rw [hfinal]
    have hk := g.finite_class_kernel_bound hd hG hbudget z q hz hq R hR smallG b.val j.val
    have hfar := (exceptional_port_distance g.graph hG S i.val j.val r hcontain b hb).2
    exact hk.trans (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one ht htone hfar) hCbar)
  have houtside := outside_graph_diameter_bound g.graph hG S hS (finiteOmega d) hbudget.excess_le R hR
  have hmass : (∑ a, ∑ b, ‖W a b‖) ≤ M :=
    g.finite_class_exceptionalSelfEnergy_mass hd S hzero hG hS hbudget q z hz hq
      ((finiteOmega d + 1) * (2 * R + 1)) houtside smallOutside
  have hsplit := schur_localization_split_bound A W E hA hordinary hfull model.boundaryCoefficient τ hτ hE
    K B Cbar C₀ ((Rs : ℝ) + 1) (model.boundaryCoefficient_nonnegative hd)
    (fun a b => (model.referenceDecay_pos hd z a b).le) (model.referenceCompanion_pos hd z)
    hCbar hC₀ (by positivity) href (model.referenceCompanion_diameter_bound hd z Rs hRs) hconv smallOrdinary
    (exceptionalPorts g.graph S) (g.exceptionalSelfEnergy_support S q z) i j ρ Cbar M hρ hCbar hnear hcol hmass
  rw [hfinal] at hsplit
  have hBfour : B i j ≤ 4 := model.referenceCompanion_le_four hd z i j
  have hfirst := mul_le_mul_of_nonneg_left hBfour (by positivity : 0 ≤ 2 * τ * Cbar ^ 2 * C₀)
  have hρsquare : ρ ^ 2 = physicalTransfer d z ^ (2 * r) := by
    dsimp only [ρ]
    rw [← pow_mul, Nat.mul_comm r 2]
  change ‖F i j - model.extensionGreen q z i j‖ ≤ _
  rw [norm_sub_rev]
  apply hsplit.trans
  apply (add_le_add_right hfirst _).trans_eq
  rw [hρsquare]
  dsimp only [Cbar, C, C₀, τ, M]
  ring

/-- A finite generalized Proposition 2.14. All reference, component,
inverse and localization conclusions are derived from the actual graph.
The hypotheses retain true intrinsic diameter caps and explicit finite
feedback budgets, suitable for later source-parameter instantiation. -/
theorem finite_model_localization (g : DeficientGraph V d) (hd : 3 ≤ d)
    (S : Set V) (hG : g.graph.Connected) (hS : (g.graph.induce S).Connected)
    (hbudget : g.FiniteReferenceBudget)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) (Bcap : ℝ) (hBcap : ‖z‖ ≤ Bcap)
    (R Rs : ℕ) (hR : ∀ a b, g.graph.dist a b ≤ R)
    (hRs : ∀ a b, (g.graph.induce S).dist a b ≤ Rs)
    (smallG : ‖q - semicircleRoot z‖ * finiteExtraReferenceConstant d *
      coreConvolutionConstant (finiteOmega d + 1) * ((R : ℝ) + 1) ≤ 1 / 2)
    (smallS : ‖q - semicircleRoot z‖ * finiteExtraReferenceConstant d *
      coreConvolutionConstant (finiteOmega d + 1) * ((Rs : ℝ) + 1) ≤ 1 / 2)
    (smallOutside : ‖q - semicircleRoot z‖ * finiteExtraReferenceConstant d *
      coreConvolutionConstant (finiteOmega d + 1) * (((finiteOmega d + 1) * (2 * R + 1) : ℕ) + 1 : ℝ) ≤ 1 / 2)
    (smallCavity : ‖q - semicircleRoot z‖ * 3 * (3 / 2 : ℝ) * ((2 * R : ℕ) + 1 : ℝ) ≤ 1 / 2)
    (smallOrdinary : ordinaryFeedbackBudget z q Bcap R * (2 * finiteExtraReferenceConstant d) *
      coreConvolutionConstant (finiteOmega d + 1) * ((Rs : ℝ) + 1) ≤ 1 / 2)
    (i j : S) (r : ℕ) (hcontain : pairBallVertices g.graph i.val j.val r ⊆ S) :
    ‖g.extensionGreen q z i.val j.val - (g.restrict S).extensionGreen q z i j‖ ≤
      32 * finiteExtraReferenceConstant d ^ 2 * coreConvolutionConstant (finiteOmega d + 1) *
        ordinaryFeedbackBudget z q Bcap R +
      (8 * finiteExtraReferenceConstant d ^ 2 * localizationExceptionalMass d q +
        4 * finiteExtraReferenceConstant d ^ 2 * ‖q‖ *
          (((finiteOmega d : ℝ) + 1) / ((d : ℝ) - 1))) * physicalTransfer d z ^ (2 * r) := by
  let g' := g.clearOutsideDeficit S
  have hzero : ∀ v ∉ S, g'.deficit v = 0 := by
    intro v hv
    exact if_neg hv
  have hlocal := g'.exterior_zero_schur_localization hd S hzero hG hS
    (g.clearOutsideDeficit_budget S hbudget) q z hz hq Bcap hBcap R Rs hR hRs
    smallG smallS smallOutside smallCavity smallOrdinary i j r hcontain
  change ‖(g.clearOutsideDeficit S).extensionGreen q z i.val j.val -
    ((g.clearOutsideDeficit S).restrict S).extensionGreen q z i j‖ ≤ _ at hlocal
  rw [g.clearOutsideDeficit_restricted_Green S q z] at hlocal
  have hdeficit := g.clearOutsideDeficit_pairBall_localization_bound hd hG hbudget S z q hz hq
    R hR smallG i.val j.val r hcontain
  have hsplit : g.extensionGreen q z i.val j.val - (g.restrict S).extensionGreen q z i j =
      (g.extensionGreen q z i.val j.val - g'.extensionGreen q z i.val j.val) +
      (g'.extensionGreen q z i.val j.val - (g.restrict S).extensionGreen q z i j) := by ring
  rw [hsplit]
  apply (norm_add_le _ _).trans
  exact (add_le_add hdeficit hlocal).trans_eq (by ring)

end DeficientGraph
end LocalLaw
