import LocalLaw.BranchNet

/-!
# Explicit rectangular cells for a branch-preserving spectral net

Each coordinate is assigned its floor cell. Representatives selected in the
same cell and error branch are at distance at most 2h, with at most
(M+1)(K+1) times the number of branches representatives.
-/

namespace LocalLaw

private theorem interval_floor_bounds (a x h : ℝ) (M : ℕ) (hh : 0 < h)
    (hx : a ≤ x ∧ x ≤ a + (M : ℝ) * h) :
    0 ≤ Int.floor ((x - a) / h) ∧ Int.floor ((x - a) / h) ≤ (M : ℤ) := by
  constructor
  · exact Int.floor_nonneg.mpr (div_nonneg (sub_nonneg.mpr hx.1) hh.le)
  · apply Int.floor_le_iff.mpr
    have hr : (x - a) / h ≤ (M : ℝ) := by
      apply (div_le_iff₀ hh).mpr
      linarith [hx.2]
    simpa only [Int.cast_natCast] using
      (lt_of_le_of_lt hr (lt_add_one (M : ℝ)))

/-- A total cell index; its values outside the specified interval are irrelevant. -/
noncomputable def intervalCell (a h : ℝ) (M : ℕ) (hh : 0 < h) (x : ℝ) : Fin (M + 1) := by
  classical
  exact if hx : a ≤ x ∧ x ≤ a + (M : ℝ) * h then
    ⟨(Int.floor ((x - a) / h)).toNat,
      Nat.lt_succ_of_le (Int.toNat_le.mpr (interval_floor_bounds a x h M hh hx).2)⟩
    else ⟨0, Nat.zero_lt_succ M⟩

theorem intervalCell_diameter (a h : ℝ) (M : ℕ) (hh : 0 < h) (x y : ℝ)
    (hx : a ≤ x ∧ x ≤ a + (M : ℝ) * h)
    (hy : a ≤ y ∧ y ≤ a + (M : ℝ) * h)
    (hcell : intervalCell a h M hh x = intervalCell a h M hh y) : |x - y| ≤ h := by
  have hval := congrArg Fin.val hcell
  simp only [intervalCell, dif_pos hx, dif_pos hy] at hval
  have hf : Int.floor ((x - a) / h) = Int.floor ((y - a) / h) := by
    calc
      _ = ((Int.floor ((x - a) / h)).toNat : ℤ) :=
        (Int.toNat_of_nonneg (interval_floor_bounds a x h M hh hx).1).symm
      _ = ((Int.floor ((y - a) / h)).toNat : ℤ) := congrArg Int.ofNat hval
      _ = _ := Int.toNat_of_nonneg (interval_floor_bounds a y h M hh hy).1
  have hxl := mul_le_mul_of_nonneg_right (Int.floor_le ((x - a) / h)) hh.le
  have hxu := mul_lt_mul_of_pos_right (Int.lt_floor_add_one ((x - a) / h)) hh
  have hyl := mul_le_mul_of_nonneg_right (Int.floor_le ((y - a) / h)) hh.le
  have hyu := mul_lt_mul_of_pos_right (Int.lt_floor_add_one ((y - a) / h)) hh
  rw [div_mul_cancel₀ _ (ne_of_gt hh)] at hxl hxu hyl hyu
  rw [hf] at hxl hxu
  apply abs_le.mpr
  constructor <;> nlinarith

/-- Closed rectangle covered by M+1 horizontal and K+1 vertical floor cells. -/
def spectralRectangle (a b h : ℝ) (M K : ℕ) : Set ℂ :=
  {z | (a ≤ z.re ∧ z.re ≤ a + (M : ℝ) * h) ∧
    (b ≤ z.im ∧ z.im ≤ b + (K : ℝ) * h)}

noncomputable def rectangularCell (a b h : ℝ) (M K : ℕ) (hh : 0 < h)
    (z : ℂ) : Fin (M + 1) × Fin (K + 1) :=
  (intervalCell a h M hh z.re, intervalCell b h K hh z.im)

theorem rectangularCell_diameter (a b h : ℝ) (M K : ℕ) (hh : 0 < h)
    (z w : ℂ) (hz : z ∈ spectralRectangle a b h M K)
    (hw : w ∈ spectralRectangle a b h M K)
    (hcell : rectangularCell a b h M K hh z = rectangularCell a b h M K hh w) :
    dist z w ≤ 2 * h := by
  have hx := intervalCell_diameter a h M hh z.re w.re hz.1 hw.1 (congrArg Prod.fst hcell)
  have hy := intervalCell_diameter b h K hh z.im w.im hz.2 hw.2 (congrArg Prod.snd hcell)
  calc
    dist z w = ‖z - w‖ := dist_eq_norm _ _
    _ ≤ |(z - w).re| + |(z - w).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 2 * h := by simp only [Complex.sub_re, Complex.sub_im]; linarith

/-- Finite branch-preserving net on any subset of a rectangle, with the
explicit cell count needed for a polynomial union bound. -/
theorem exists_rectangular_branchNet {J : Type*} [Fintype J]
    (D : Set ℂ) (classify : ℂ → J) (a b h : ℝ) (M K : ℕ) (hh : 0 < h)
    (hD : D ⊆ spectralRectangle a b h M K) :
    Nonempty (BranchNet D classify (2 * h) ((M + 1) * (K + 1) * Fintype.card J)) := by
  have hn := exists_branchNet D (rectangularCell a b h M K hh) classify (2 * h)
    (by
      intro z hz w hw heq
      exact rectangularCell_diameter a b h M K hh z w (hD hz) (hD hw) heq)
  simpa only [Fintype.card_prod, Fintype.card_fin] using hn

end LocalLaw
