import LocalLaw.ExteriorResolvent
import LocalLaw.MatrixEntryStability

/-!
# Finite resolvent localization by matching moments

A finite polynomial truncation and an explicit remainder replace an infinite
Neumann expansion. Two matrices may have different finite index types: equality
of the selected entries of their first K powers yields a resolvent comparison.
Strict row-sum dominance proves both inverse/unit obligations.
-/

open scoped BigOperators

namespace LocalLaw

section FiniteTruncation

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Row absolute-sum bounds propagate to every matrix power. -/
theorem matrix_power_row_sum_bound (H : Matrix V V ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hrow : ∀ i, (∑ k, ‖H i k‖) ≤ M) (n : ℕ) :
    ∀ i, (∑ j, ‖(H ^ n) i j‖) ≤ M ^ n := by
  induction n with
  | zero =>
    intro i
    simp only [pow_zero]
    simp_rw [Matrix.one_apply, apply_ite norm, norm_one, norm_zero]
    simp [eq_comm]
  | succ n ih =>
    intro i
    rw [pow_succ]
    calc
      (∑ j, ‖(H ^ n * H) i j‖) ≤ ∑ j, ∑ k, ‖(H ^ n) i k‖ * ‖H k j‖ :=
        Finset.sum_le_sum (fun j _ => matrix_mul_entry_norm_le _ _ i j)
      _ = ∑ k, ‖(H ^ n) i k‖ * ∑ j, ‖H k j‖ := by
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
      _ ≤ ∑ k, ‖(H ^ n) i k‖ * M := Finset.sum_le_sum (fun k _ =>
        mul_le_mul_of_nonneg_left (hrow k) (norm_nonneg _))
      _ = (∑ k, ‖(H ^ n) i k‖) * M := (Finset.sum_mul ..).symm
      _ ≤ M ^ n * M := mul_le_mul_of_nonneg_right (ih i) hM
      _ = M ^ (n + 1) := (pow_succ M n).symm

/-- The finite spectral resolvent polynomial through power K-1. -/
noncomputable def resolventPolynomial (H : Matrix V V ℂ) (z : ℂ) (K : ℕ) : Matrix V V ℂ :=
  -(∑ n ∈ Finset.range K, (z⁻¹) ^ (n + 1) • H ^ n)

/-- Exact finite truncation identity, with no convergence premise. -/
theorem green_finite_truncation (H : Matrix V V ℂ) (z : ℂ) (hz : z ≠ 0)
    (hunit : IsUnit (spectralMatrix H z)) (K : ℕ) :
    green H z = resolventPolynomial H z K + (z⁻¹) ^ K • (H ^ K * green H z) := by
  let G := green H z
  let α := z⁻¹
  have hprod : H * G - z • G = 1 := by
    have h := Matrix.mul_nonsing_inv (spectralMatrix H z)
      ((Matrix.isUnit_iff_isUnit_det _).mp hunit)
    simpa only [spectralMatrix, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul] using h
  have hscalar : z • G = H * G - 1 := by
    rw [eq_sub_iff_add_eq]
    have h := sub_eq_iff_eq_add.mp hprod
    simpa only [add_comm] using h.symm
  have hbase : G = -α • (1 : Matrix V V ℂ) + α • (H * G) := by
    calc
      G = α • (z • G) := by simp only [α, smul_smul, inv_mul_cancel₀ hz, one_smul]
      _ = α • (H * G - 1) := by rw [hscalar]
      _ = -α • (1 : Matrix V V ℂ) + α • (H * G) := by
        simp only [smul_sub, neg_smul]
        abel
  change G = resolventPolynomial H z K + α ^ K • (H ^ K * G)
  induction K with
  | zero => simp [resolventPolynomial]
  | succ K ih =>
    have hrem : α ^ K • (H ^ K * G) =
        -(α ^ (K + 1) • H ^ K) + α ^ (K + 1) • (H ^ (K + 1) * G) := by
      calc
        α ^ K • (H ^ K * G) = α ^ K • (H ^ K * (-α • 1 + α • (H * G))) :=
          congrArg (fun A : Matrix V V ℂ => α ^ K • (H ^ K * A)) hbase
        _ = -(α ^ (K + 1) • H ^ K) + α ^ (K + 1) • (H ^ (K + 1) * G) := by
          simp only [Matrix.mul_add, Matrix.mul_neg, Matrix.mul_smul, Matrix.mul_one,
            smul_add, smul_neg, smul_smul, pow_succ, Matrix.mul_assoc, neg_smul]
    calc
      G = resolventPolynomial H z K + α ^ K • (H ^ K * G) := ih
      _ = resolventPolynomial H z (K + 1) + α ^ (K + 1) • (H ^ (K + 1) * G) := by
        rw [hrem]
        simp only [resolventPolynomial, Finset.sum_range_succ, α]
        abel

/-- The explicit finite remainder estimate follows from row-power control and
the actual inverse entry bound. -/
theorem green_truncation_remainder_bound (H : Matrix V V ℂ) (z : ℂ) (M : ℝ)
    (hM : 0 ≤ M) (hrow : ∀ i, (∑ k, ‖H i k‖) ≤ M)
    (hgap : M < ‖z‖) (K : ℕ) (i j : V) :
    ‖green H z i j - resolventPolynomial H z K i j‖ ≤
      (M / ‖z‖) ^ K / (‖z‖ - M) := by
  have hzn : 0 < ‖z‖ := hM.trans_lt hgap
  have hz : z ≠ 0 := norm_pos_iff.mp hzn
  have hunit := spectralMatrix_isUnit_of_row_gap H z M hrow hgap
  have hden : 0 < ‖z‖ - M := sub_pos.mpr hgap
  have hidentity := congrArg (fun A : Matrix V V ℂ => A i j)
    (green_finite_truncation H z hz hunit K)
  have hentry : green H z i j - resolventPolynomial H z K i j =
      (z⁻¹) ^ K * (H ^ K * green H z) i j := by
    change green H z i j = resolventPolynomial H z K i j +
      (z⁻¹) ^ K * (H ^ K * green H z) i j at hidentity
    exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using hidentity)
  rw [hentry, norm_mul, norm_pow, norm_inv]
  have hbound := matrix_mul_entry_bound_of_row (H ^ K) (green H z) i j (M ^ K)
    (1 / (‖z‖ - M)) (by positivity) (matrix_power_row_sum_bound H M hM hrow K i)
    (fun k => exterior_green_entry_bound H z M hrow hgap hunit k j)
  calc
    (‖z‖⁻¹) ^ K * ‖(H ^ K * green H z) i j‖ ≤
        (‖z‖⁻¹) ^ K * (M ^ K * (1 / (‖z‖ - M))) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = (M / ‖z‖) ^ K / (‖z‖ - M) := by
      rw [div_pow]
      simp only [div_eq_mul_inv, inv_pow]
      ring

end FiniteTruncation

section MomentMatching

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- Matching root-entry moments for matrices of different dimensions gives
the actual exterior resolvent localization bound. -/
theorem resolvent_moment_matching_bound (H : Matrix I I ℂ) (B : Matrix J J ℂ)
    (z : ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hHrow : ∀ i, (∑ k, ‖H i k‖) ≤ M) (hBrow : ∀ i, (∑ k, ‖B i k‖) ≤ M)
    (hgap : M < ‖z‖) (K : ℕ) (i j : I) (a b : J)
    (moments : ∀ n < K, (H ^ n) i j = (B ^ n) a b) :
    ‖green H z i j - green B z a b‖ ≤ 2 * (M / ‖z‖) ^ K / (‖z‖ - M) := by
  have hpoly : resolventPolynomial H z K i j = resolventPolynomial B z K a b := by
    unfold resolventPolynomial
    simp only [Matrix.neg_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    rw [moments n (Finset.mem_range.mp hn)]
  have hH := green_truncation_remainder_bound H z M hM hHrow hgap K i j
  have hB := green_truncation_remainder_bound B z M hM hBrow hgap K a b
  calc
    ‖green H z i j - green B z a b‖ ≤
        ‖green H z i j - resolventPolynomial H z K i j‖ +
        ‖resolventPolynomial H z K i j - green B z a b‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = ‖green H z i j - resolventPolynomial H z K i j‖ +
        ‖green B z a b - resolventPolynomial B z K a b‖ := by
      rw [hpoly, norm_sub_rev (resolventPolynomial B z K a b) (green B z a b)]
    _ ≤ (M / ‖z‖) ^ K / (‖z‖ - M) + (M / ‖z‖) ^ K / (‖z‖ - M) := add_le_add hH hB
    _ = 2 * (M / ‖z‖) ^ K / (‖z‖ - M) := by ring

end MomentMatching

end LocalLaw
