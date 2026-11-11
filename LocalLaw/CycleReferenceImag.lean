import LocalLaw.CycleReferenceKernel

/-!
# Uniform imaginary-part bound on the actual finite cycle

A simple power-difference induction gives a uniform Lipschitz constant on
the transfer disk of radius three quarters. The verified cyclic inverse is
a real-coefficient rational function of m, so reflection controls its entire
imaginary part, uniformly in the cycle length and vertex pair.
-/

namespace LocalLaw
noncomputable section

/-- Uniform power Lipschitz bound on a strict disk, independent of the power. -/
theorem strict_disk_power_lipschitz (a b : ℂ) (ha : ‖a‖ ≤ 3 / 4) (hb : ‖b‖ ≤ 3 / 4) (n : ℕ) :
    ‖a ^ n - b ^ n‖ ≤ 4 * ‖a - b‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hid : a ^ (n + 1) - b ^ (n + 1) = (a - b) * a ^ n + b * (a ^ n - b ^ n) := by
      rw [pow_succ, pow_succ]
      ring
    have hpow : ‖a ^ n‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (ha.trans (by norm_num))
    rw [hid]
    calc
      _ ≤ ‖(a - b) * a ^ n‖ + ‖b * (a ^ n - b ^ n)‖ := norm_add_le _ _
      _ ≤ ‖a - b‖ * 1 + (3 / 4 : ℝ) * (4 * ‖a - b‖) := by
        rw [norm_mul, norm_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left hpow (norm_nonneg _))
          (mul_le_mul hb ih (norm_nonneg _) (by norm_num))
      _ = _ := by ring

/-- The analytic cycle kernel as a real-coefficient function of the free root. -/
def cycleAnalyticKernel (n d : ℕ) (a : ℂ) (s : Fin (n + 3)) : ℂ :=
  cycleKernelCandidate n (rationalTreeReference (d - 1) a) (-a * treeEdgeWeight d) s

theorem cycle_transfer_lipschitz (d : ℕ) (hd : 3 ≤ d) (a b : ℂ) :
    ‖-a * treeEdgeWeight d - (-b * treeEdgeWeight d)‖ ≤ (3 / 4 : ℝ) * ‖a - b‖ := by
  have hα : ‖treeEdgeWeight d‖ ≤ 3 / 4 := by
    simpa only [neg_one_mul, norm_neg] using
      cycle_transfer_norm_le_three_quarters d hd (1 : ℂ) (by norm_num)
  have hid : -a * treeEdgeWeight d - (-b * treeEdgeWeight d) = -(a - b) * treeEdgeWeight d := by ring
  rw [hid, norm_mul, norm_neg]
  exact (mul_le_mul_of_nonneg_left hα (norm_nonneg _)).trans_eq (mul_comm _ _)

/-- A coarse but length-independent Lipschitz constant for the entire cyclic
kernel on the closed unit disk. -/
theorem cycleAnalyticKernel_lipschitz (n d : ℕ) (hd : 3 ≤ d) (a b : ℂ)
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (s : Fin (n + 3)) :
    ‖cycleAnalyticKernel n d a s - cycleAnalyticKernel n d b s‖ ≤ 128 * ‖a - b‖ := by
  let ta := -a * treeEdgeWeight d
  let tb := -b * treeEdgeWeight d
  let pa := rationalTreeReference (d - 1) a
  let pb := rationalTreeReference (d - 1) b
  let Na := ta ^ s.val + ta ^ (n + 3 - s.val)
  let Nb := tb ^ s.val + tb ^ (n + 3 - s.val)
  let Da := 1 - ta ^ (n + 3)
  let Db := 1 - tb ^ (n + 3)
  let δ := ‖a - b‖
  have hδ : 0 ≤ δ := norm_nonneg _
  have hta : ‖ta‖ ≤ 3 / 4 := cycle_transfer_norm_le_three_quarters d hd a ha
  have htb : ‖tb‖ ≤ 3 / 4 := cycle_transfer_norm_le_three_quarters d hd b hb
  have htlip : ‖ta - tb‖ ≤ (3 / 4 : ℝ) * δ := cycle_transfer_lipschitz d hd a b
  have hpow : ∀ k, ‖ta ^ k - tb ^ k‖ ≤ 3 * δ := by
    intro k
    exact (strict_disk_power_lipschitz ta tb hta htb k).trans (by nlinarith)
  have hpowA : ∀ k, ‖ta ^ k‖ ≤ 1 := by intro k; rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hta.trans (by norm_num))
  have hpowB : ∀ k, ‖tb ^ k‖ ≤ 1 := by intro k; rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (htb.trans (by norm_num))
  have hNa : ‖Na‖ ≤ 2 := (norm_add_le _ _).trans (by linarith [hpowA s.val, hpowA (n + 3 - s.val)])
  have hNb : ‖Nb‖ ≤ 2 := (norm_add_le _ _).trans (by linarith [hpowB s.val, hpowB (n + 3 - s.val)])
  have hNlip : ‖Na - Nb‖ ≤ 6 * δ := by
    have hid : Na - Nb = (ta ^ s.val - tb ^ s.val) + (ta ^ (n + 3 - s.val) - tb ^ (n + 3 - s.val)) := by dsimp [Na, Nb]; ring
    rw [hid]
    exact (norm_add_le _ _).trans (by linarith [hpow s.val, hpow (n + 3 - s.val)])
  have hDlip : ‖Db - Da‖ ≤ 3 * δ := by
    have hid : Db - Da = ta ^ (n + 3) - tb ^ (n + 3) := by dsimp [Da, Db]; ring
    rw [hid]
    exact hpow _
  have hDa : 1 / 2 ≤ ‖Da‖ := cycle_denominator_norm_lower n d hd a ha
  have hDb : 1 / 2 ≤ ‖Db‖ := cycle_denominator_norm_lower n d hd b hb
  have hDa0 : Da ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hDa)
  have hDb0 : Db ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hDb)
  have hpLip : ‖pa - pb‖ ≤ 6 * δ := rationalTreeReference_lipschitz (d - 1) (by omega) a b ha hb
  have hpB : ‖pb‖ ≤ 2 := rationalTreeReference_norm_le_two (d - 1) (by omega) b hb
  have hid : pa * Na / Da - pb * Nb / Db =
      (pa - pb) * Na / Da + pb * (Na - Nb) / Da + pb * Nb * (Db - Da) / (Da * Db) := by
    field_simp
    ring
  have h₁ : ‖(pa - pb) * Na / Da‖ ≤ 24 * δ := by
    rw [norm_div, norm_mul]
    calc
      _ ≤ ((6 * δ) * 2) / (1 / 2) :=
        div_le_div₀ (by positivity) (mul_le_mul hpLip hNa (norm_nonneg _) (by positivity)) (by norm_num) hDa
      _ = _ := by ring
  have h₂ : ‖pb * (Na - Nb) / Da‖ ≤ 24 * δ := by
    rw [norm_div, norm_mul]
    calc
      _ ≤ (2 * (6 * δ)) / (1 / 2) :=
        div_le_div₀ (by positivity) (mul_le_mul hpB hNlip (norm_nonneg _) (by norm_num)) (by norm_num) hDa
      _ = _ := by ring
  have h₃ : ‖pb * Nb * (Db - Da) / (Da * Db)‖ ≤ 48 * δ := by
    rw [norm_div, norm_mul, norm_mul, norm_mul]
    have hnum : ‖pb‖ * ‖Nb‖ * ‖Db - Da‖ ≤ 4 * (3 * δ) := by
      have hprod : ‖pb‖ * ‖Nb‖ ≤ 4 := by nlinarith [norm_nonneg pb, norm_nonneg Nb]
      exact mul_le_mul hprod hDlip (norm_nonneg _) (by norm_num)
    have hden : 1 / 4 ≤ ‖Da‖ * ‖Db‖ := by nlinarith
    calc
      _ ≤ (4 * (3 * δ)) / (1 / 4) := div_le_div₀ (by positivity) hnum (by norm_num) hden
      _ = _ := by ring
  change ‖pa * Na / Da - pb * Nb / Db‖ ≤ 128 * δ
  rw [hid]
  exact (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans (by linarith))

/-- Real coefficients give exact reflection across the real axis. -/
theorem cycleAnalyticKernel_conj (n d : ℕ) (a : ℂ) (s : Fin (n + 3)) :
    cycleAnalyticKernel n d (starRingEnd ℂ a) s = starRingEnd ℂ (cycleAnalyticKernel n d a s) := by
  simp [cycleAnalyticKernel, cycleKernelCandidate, rationalTreeReference, treeEdgeWeight,
    map_div, map_mul, map_sub, map_add, map_pow]

/-- Reflection turns the uniform disk Lipschitz estimate into a uniform
imaginary-part bound for the analytic cycle kernel. -/
theorem cycleAnalyticKernel_im_bound (n d : ℕ) (hd : 3 ≤ d) (a : ℂ)
    (ha : ‖a‖ ≤ 1) (haim : 0 ≤ a.im) (s : Fin (n + 3)) :
    |(cycleAnalyticKernel n d a s).im| ≤ 128 * a.im := by
  let F := cycleAnalyticKernel n d a s
  have hconj : ‖starRingEnd ℂ a‖ ≤ 1 := by simpa only [Complex.norm_conj] using ha
  have hh := cycleAnalyticKernel_lipschitz n d hd a (starRingEnd ℂ a) ha hconj s
  rw [cycleAnalyticKernel_conj] at hh
  have hnorm : ∀ w : ℂ, ‖w - starRingEnd ℂ w‖ = 2 * |w.im| := by
    intro w
    rw [Complex.sub_conj, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul]
    norm_num
  rw [hnorm, hnorm, abs_of_nonneg haim] at hh
  linarith

/-- Uniform actual finite-cycle imaginary-part bound at every pair. -/
theorem cycleReferenceMatrix_im_bound (n d : ℕ) (hd : 3 ≤ d) (z : ℂ)
    (hz : 0 < z.im) (i j : Fin (n + 3)) :
    |((cycleReferenceMatrix n d (semicircleRoot z) z)⁻¹ i j).im| ≤ 128 * (semicircleRoot z).im := by
  rw [cycleReferenceMatrix_inverse n d hd (semicircleRoot z) z (semicircleRoot_equation z)
    (semicircleRoot_norm_le_one z) hz (semicircleRoot_im_pos hz).le]
  have hp : kestenMcKayTransform d (semicircleRoot z) z = rationalTreeReference (d - 1) (semicircleRoot z) :=
    kestenMcKayTransform_eq d hd _ z (semicircleRoot_equation z) hz (semicircleRoot_im_pos hz).le
  rw [hp]
  exact cycleAnalyticKernel_im_bound n d hd _ (semicircleRoot_norm_le_one z) (semicircleRoot_im_pos hz).le _

end
end LocalLaw
