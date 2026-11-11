import LocalLaw.CommonBallObservation
import LocalLaw.ScalarPriorRescale
import LocalLaw.SourceDeletionParameters

/-!
# Finite source budgets for the singleton observation

A fixed scalar-prior constant is absorbed into C^2*epsilon. The source
L^3*epsilon approximation then dominates both localization errors and pays
the scalar pivot smallness once the stated fixed constants lie below L.
-/

noncomputable section
namespace LocalLaw
namespace DeficientGraph

def singletonObservationConstant (d : ℕ) : ℝ :=
  4 * (2 * finiteExtraReferenceConstant d * (d : ℝ) + 1) ^ 2 + 1

def singletonPivotConstant (d : ℕ) (B : ℝ) : ℝ :=
  (d : ℝ) + B + 4 + 2 * finiteExtraReferenceConstant d * (d : ℝ) ^ 2

theorem singleton_observation_source_budgets (d : ℕ) (hd : 3 ≤ d)
    (z q : ℂ) (hz : 0 < z.im) (B ε L A C : ℝ)
    (hB : ‖z‖ ≤ B) (hε : 0 ≤ ε) (hL : 1 ≤ L) (hA : 0 ≤ A) (hC : 1 ≤ C)
    (hcap : (C ^ 2 * ε) * L ^ 4 ≤ 1)
    (hprior : ‖q - semicircleRoot z‖ ≤ C * scalarScale (spectralScale z) ε)
    (hfeedback : localizationWeakConstant d B A * C ≤ L ^ 2)
    (hpivot : 4 * singletonPivotConstant d B ≤ L) :
    singletonPivotBudget d q z (2 * finiteExtraReferenceConstant d) *
      (C * L ^ 3 * ε + localizationWeakConstant d B A * L * (C ^ 2 * ε)) ≤ 1 / 2 ∧
    singletonObservationBudget d B A L (C ^ 2 * ε) (C * L ^ 3 * ε) ≤
      singletonObservationConstant d * (C * L ^ 3 * ε) := by
  let K := localizationWeakConstant d B A
  let P := singletonPivotConstant d B
  let δ := C * L ^ 3 * ε
  let E := K * L * (C ^ 2 * ε)
  have hLpos : 0 < L := by linarith
  have hC0 : 0 ≤ C := by linarith
  have hC2 : C ≤ C ^ 2 := by nlinarith
  have hK : 0 ≤ K := (by norm_num : (0 : ℝ) ≤ 1).trans
    (localizationWeakConstant_ge_one d hd B A hA)
  have hδ : 0 ≤ δ := by dsimp only [δ]; positivity
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hδL : δ * L ≤ 1 := by
    calc
      _ = C * (ε * L ^ 4) := by dsimp only [δ]; ring
      _ ≤ C ^ 2 * (ε * L ^ 4) := mul_le_mul_of_nonneg_right hC2 (by positivity)
      _ = (C ^ 2 * ε) * L ^ 4 := by ring
      _ ≤ _ := hcap
  have hEδ : E ≤ δ := by
    have hh := mul_le_mul_of_nonneg_right hfeedback (by positivity : 0 ≤ C * L * ε)
    convert hh using 1 <;> dsimp only [E, δ, K] <;> ring
  have hεscaled : 0 ≤ C ^ 2 * ε := by positivity
  have hεone : C ^ 2 * ε ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left (show 1 ≤ L ^ 4 from one_le_pow₀ hL) hεscaled
    nlinarith only [hh, hcap]
  have hpriorScaled := hprior.trans
    (scalarScale_constant_absorption (spectralScale z) ε C (spectralScale_pos hz) hε hC)
  have hq := weak_boundary_norm_le_two z q hz (C ^ 2 * ε) hεscaled hεone hpriorScaled
  have hCref : 0 ≤ finiteExtraReferenceConstant d := (by norm_num : (0 : ℝ) ≤ 1).trans
    (finiteExtraReferenceConstant_ge_one d hd)
  have hB0 : 0 ≤ B := (norm_nonneg z).trans hB
  have hP : 0 ≤ P := by dsimp only [P, singletonPivotConstant]; positivity
  have hPivotCap : singletonPivotBudget d q z (2 * finiteExtraReferenceConstant d) ≤ P := by
    dsimp only [singletonPivotBudget, P, singletonPivotConstant]
    nlinarith only [hB, hq]
  have hhalf : P * (2 * δ) ≤ 1 / 2 := by
    apply (mul_le_mul_right hLpos).mp
    have hh := mul_le_mul_of_nonneg_left hδL (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hP)
    nlinarith only [hh, hpivot]
  constructor
  · change singletonPivotBudget d q z (2 * finiteExtraReferenceConstant d) * (δ + E) ≤ 1 / 2
    calc
      _ ≤ P * (δ + E) := mul_le_mul_of_nonneg_right hPivotCap (add_nonneg hδ hE)
      _ ≤ P * (2 * δ) := mul_le_mul_of_nonneg_left (by linarith only [hEδ]) hP
      _ ≤ _ := hhalf
  · have hh := mul_le_mul_of_nonneg_left hEδ
      (by positivity : 0 ≤ 2 * (2 * finiteExtraReferenceConstant d * (d : ℝ) + 1) ^ 2 + 1)
    change 2 * (2 * finiteExtraReferenceConstant d * (d : ℝ) + 1) ^ 2 * (δ + E) + E ≤
      singletonObservationConstant d * δ
    dsimp only [singletonObservationConstant]
    nlinarith only [hh]

end DeficientGraph
end LocalLaw
