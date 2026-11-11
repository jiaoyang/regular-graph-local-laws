import LocalLaw.GuardedOutsideMean

/-!
# A one-edge mean from exact good-edge identities

A good sample identifies the reference value with an actual bounded cavity
plus the bounded observation. Thus its bound is proved, and the entire mean
error is controlled by the actual exceptional sampling density.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance finiteExceptionalBiasDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Finite averaging with a literal exceptional subset. -/
theorem finiteComplexMean_exceptional_difference {E : Type*} [Fintype E]
    (p : E → Prop) (f g : E → ℂ) (C : ℝ)
    (hgood : ∀ e, p e → f e = g e) (hbad : ∀ e, ¬p e → ‖f e - g e‖ ≤ C) :
    ‖finiteComplexMean f - finiteComplexMean g‖ ≤
      (Fintype.card E : ℝ)⁻¹ * (Nat.card {e : E // ¬p e} : ℝ) * C := by
  unfold finiteComplexMean
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), ← Finset.sum_sub_distrib]
  have hp : ∀ e, ‖f e - g e‖ ≤ (if ¬p e then C else 0) := by
    intro e
    by_cases he : p e
    · simp [he, hgood e he]
    · simpa only [he, not_false_eq_true, if_true] using hbad e he
  have hs : (∑ e : E, if ¬p e then C else 0) = (Nat.card {e : E // ¬p e} : ℝ) * C := by
    simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  calc
    _ ≤ (Fintype.card E : ℝ)⁻¹ * (∑ e : E, if ¬p e then C else 0) :=
      mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun e _ => hp e))) (by positivity)
    _ = _ := by rw [hs]; ring

/-- A reference cap follows from one actual good sample. -/
theorem cavity_reference_cap_of_good_sample {E : Type*} (p : E → Prop)
    (Z f : E → ℂ) (Y : ℂ) (b M : ℝ)
    (hZ : ∀ e, ‖Z e‖ ≤ b) (hf : ∀ e, ‖f e‖ ≤ M)
    (hgood : ∀ e, p e → Z e = f e - Y) (hex : ∃ e, p e) : ‖Y‖ ≤ M + b := by
  obtain ⟨e, he⟩ := hex
  have hY : Y = f e - Z e := by rw [hgood e he]; ring
  rw [hY]
  exact (norm_sub_le _ _).trans (add_le_add (hf e) (hZ e))

/-- The finite one-edge bias uses only actual bounded observations, actual
bounded cavities, a good-edge equality, and the actual exceptional count. -/
theorem finiteComplexMean_cavity_bias {E : Type*} [Fintype E] [Nonempty E]
    (p : E → Prop) (Z f : E → ℂ) (Y Q : ℂ) (b M δ : ℝ)
    (hZ : ∀ e, ‖Z e‖ ≤ b) (hf : ∀ e, ‖f e‖ ≤ M)
    (hgood : ∀ e, p e → Z e = f e - Y) (hex : ∃ e, p e)
    (hQ : ‖finiteComplexMean f - Q‖ ≤ δ) :
    ‖finiteComplexMean Z - (Q - Y)‖ ≤
      (Fintype.card E : ℝ)⁻¹ * (Nat.card {e : E // ¬p e} : ℝ) * (2 * (M + b)) + δ := by
  have hY := cavity_reference_cap_of_good_sample p Z f Y b M hZ hf hgood hex
  have hbad : ∀ e, ¬p e → ‖Z e - (f e - Y)‖ ≤ 2 * (M + b) := by
    intro e _
    have hh := (norm_sub_le (Z e) (f e - Y)).trans
      (add_le_add (hZ e) ((norm_sub_le (f e) Y).trans (add_le_add (hf e) hY)))
    exact hh.trans_eq (by ring)
  have hmean := finiteComplexMean_exceptional_difference p Z (fun e => f e - Y)
    (2 * (M + b)) hgood hbad
  rw [finiteComplexMean_sub_const] at hmean
  have hsecond : ‖(finiteComplexMean f - Y) - (Q - Y)‖ ≤ δ := by
    simpa only [sub_sub_sub_cancel_right] using hQ
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hmean hsecond)

end LocalLaw
