import LocalLaw.SpectralGap

/-! # Continuity of the regularized edge-distance scale -/

namespace LocalLaw

theorem min_variation_bound (a b c d D : ℝ) (hac : |a - c| ≤ D) (hbd : |b - d| ≤ D) :
    |min a b - min c d| ≤ D := by
  have ha := abs_le.mp hac
  have hb := abs_le.mp hbd
  have hforward : min a b ≤ min c d + D := by
    have h := min_le_min (show a ≤ c + D by linarith) (show b ≤ d + D by linarith)
    simpa only [min_add_add_right] using h
  have hbackward : min c d ≤ min a b + D := by
    have h := min_le_min (show c ≤ a + D by linarith) (show d ≤ b + D by linarith)
    simpa only [min_add_add_right] using h
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem edgeDistance_lipschitz (z w : ℂ) : |edgeDistance z - edgeDistance w| ≤ dist z w := by
  have hd : ∀ c : ℝ, abs (abs (z.re - c) - abs (w.re - c)) ≤ |z.re - w.re| := by
    intro c
    have h := abs_norm_sub_norm_le (z.re - c) (w.re - c)
    have heq : (z.re - c) - (w.re - c) = z.re - w.re := by ring
    simpa only [Real.norm_eq_abs, heq] using h
  have hmin := min_variation_bound |z.re - 2| |z.re + 2| |w.re - 2| |w.re + 2|
    |z.re - w.re| (hd 2) (by simpa only [sub_neg_eq_add] using hd (-2))
  have hre : |z.re - w.re| ≤ dist z w := by
    simpa only [dist_eq_norm, Complex.sub_re] using Complex.abs_re_le_norm (z - w)
  exact hmin.trans hre

theorem spectralScale_lipschitz (z w : ℂ) : |spectralScale z - spectralScale w| ≤ 2 * dist z w := by
  have hk := edgeDistance_lipschitz z w
  have hi : |z.im - w.im| ≤ dist z w := by
    simpa only [dist_eq_norm, Complex.sub_im] using Complex.abs_im_le_norm (z - w)
  have hid : spectralScale z - spectralScale w =
      (edgeDistance z - edgeDistance w) + (z.im - w.im) := by
    unfold spectralScale
    ring
  rw [hid]
  exact (abs_add_le _ _).trans (by linarith)

end LocalLaw
