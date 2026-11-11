import LocalLaw.ActualBoundaryWeights
import LocalLaw.LocalErrorBudgets

/-!
# The actual logarithmic concentration gain of Green-product weights

Physical transfer is bounded by the reciprocal square-root volume. A true
linear-log diameter cap then turns the squared-weight budget into the
log-squared tolerance needed for source local improvement.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance boundaryWeightParameterDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem resamplingDecayDenominator_pos (d ell : ℕ) (hd : 3 ≤ d) :
    0 < resamplingDecayDenominator d ell := by
  unfold resamplingDecayDenominator
  apply Real.sqrt_pos.mpr
  have hk : (0 : ℝ) < ((d - 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
  positivity

theorem physicalTransfer_resampling_gain (d ell : ℕ) (hd : 3 ≤ d) (z : ℂ) :
    physicalTransfer d z ^ ell ≤ (resamplingDecayDenominator d ell)⁻¹ := by
  let D := resamplingDecayDenominator d ell
  have hD : 0 < D := resamplingDecayDenominator_pos d ell hd
  have ht : 0 ≤ physicalTransfer d z ^ ell := pow_nonneg (physicalTransfer_pos d hd z).le _
  have htail := physical_transfer_two_sided_tail d hd z ell
  have hDsq : D ^ 2 = (((d - 1 : ℕ) : ℝ) ^ ell) := Real.sq_sqrt (by positivity)
  have hDsqpos : 0 < D ^ 2 := sq_pos_of_pos hD
  rw [← hDsq] at htail
  have htail' : (physicalTransfer d z ^ ell) ^ 2 * D ^ 2 ≤ 1 := by
    have hh := (le_div_iff₀ hDsqpos).mp (show physicalTransfer d z ^ (2 * ell) ≤ 1 / D ^ 2 by
      simpa only [one_div] using htail)
    simpa only [← pow_mul, Nat.mul_comm ell 2] using hh
  have hprod : physicalTransfer d z ^ ell * D ≤ 1 := by
    nlinarith [mul_nonneg ht hD.le]
  simpa only [one_div] using (le_div_iff₀ hD).mpr hprod

theorem square_root_weight_log_bound (x K A L D : ℝ) (R : ℕ)
    (_hx : 0 ≤ x) (hK : 0 ≤ K) (hA : 0 ≤ A) (hL : 1 ≤ L) (hD : 0 < D)
    (hR : (R : ℝ) + 1 ≤ A * L) (hbound : x ≤ K * ((R : ℝ) + 1) / D ^ 2) :
    Real.sqrt x ≤ (K * A + 1) * L / D := by
  have hLp : 0 < L := by linarith
  have hKA : 0 ≤ K * A := mul_nonneg hK hA
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · apply hbound.trans
    have hnum : K * ((R : ℝ) + 1) ≤ ((K * A + 1) * L) ^ 2 := by
      have hh := mul_le_mul_of_nonneg_left hR hK
      have hl : L ≤ L ^ 2 := by nlinarith
      nlinarith [mul_nonneg hKA (sq_nonneg L), mul_le_mul_of_nonneg_left hl hKA]
    have heq : (((K * A + 1) * L) / D) ^ 2 = (((K * A + 1) * L) ^ 2) / D ^ 2 := div_pow _ _ _
    rw [heq]
    exact div_le_div_of_nonneg_right hnum (sq_nonneg D)

namespace DeficientGraph
variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

/-- The concrete source product weights have exactly the decay and logarithmic
budgets needed by weighted concentration. No weight norm is an input. -/
theorem boundaryProductWeight_log_bounds (g : DeficientGraph V d) (hd : 3 ≤ d)
    (S : Set V) (hbudget : (g.restrict S).ComponentFiniteReferenceBudget)
    (o : V) (ell : ℕ) (hS : graphBallVertices g.graph o ell ⊆ S)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) (R : ℕ)
    (hR : ∀ a b, (g.restrict S).graph.dist a b ≤ R)
    (small : ‖q - semicircleRoot z‖ * finiteExtraReferenceConstant d *
      coreConvolutionConstant (finiteOmega d + 1) * ((R : ℝ) + 1) ≤ 1 / 2)
    (A L : ℝ) (hA : 0 ≤ A) (hL : 1 ≤ L) (hRlog : (R : ℝ) + 1 ≤ A * L) (i : S) :
    (∑ a, ‖g.boundaryProductWeight S o ell hS q z i a‖) ≤
        (8 * (d : ℝ) * finiteExtraReferenceConstant d ^ 2 * A) * L ∧
      Real.sqrt (∑ a, ‖g.boundaryProductWeight S o ell hS q z i a‖ ^ 2) ≤
        (32 * (d : ℝ) * finiteExtraReferenceConstant d ^ 4 * A + 1) * L /
          resamplingDecayDenominator d ell ∧
      ∀ a, ‖g.boundaryProductWeight S o ell hS q z i a‖ ≤
        4 * finiteExtraReferenceConstant d ^ 2 / resamplingDecayDenominator d ell := by
  obtain ⟨hl1, hl2, hmax⟩ := g.boundaryProductWeight_bounds hd S hbudget o ell hS q z hz hq R hR small i
  let D := resamplingDecayDenominator d ell
  have hD : 0 < D := resamplingDecayDenominator_pos d ell hd
  have hDsq : D ^ 2 = (((d - 1 : ℕ) : ℝ) ^ ell) := Real.sq_sqrt (by positivity)
  have htail : physicalTransfer d z ^ (2 * ell) ≤ (D ^ 2)⁻¹ := by
    rw [hDsq]
    exact physical_transfer_two_sided_tail d hd z ell
  have hdecay := physicalTransfer_resampling_gain d ell hd z
  have hkernel : 0 ≤ 32 * (d : ℝ) * finiteExtraReferenceConstant d ^ 4 := by positivity
  constructor
  · apply hl1.trans
    have hh := mul_le_mul_of_nonneg_left hRlog
      (show 0 ≤ 8 * (d : ℝ) * finiteExtraReferenceConstant d ^ 2 by positivity)
    convert hh using 1
    ring
  constructor
  · apply square_root_weight_log_bound _ (32 * (d : ℝ) * finiteExtraReferenceConstant d ^ 4)
      A L D R (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hkernel hA hL hD hRlog
    apply hl2.trans
    simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left htail
      (show 0 ≤ (32 * (d : ℝ) * finiteExtraReferenceConstant d ^ 4) * ((R : ℝ) + 1) by positivity)
  · intro a
    apply (hmax a).trans
    simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hdecay
      (show 0 ≤ 4 * finiteExtraReferenceConstant d ^ 2 by positivity)

end DeficientGraph

end LocalLaw
