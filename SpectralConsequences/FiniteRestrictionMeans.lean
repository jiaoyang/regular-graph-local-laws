import LocalLaw.OutsideCavityMean

/-! # Uniform means after excluding finitely many samples

This finite bound keeps the exact excluded-sample density. In Section 7 it
controls replacing directed edges outside T by all regular-graph edges.
-/
open scoped BigOperators
noncomputable section
namespace SpectralConsequences
open LocalLaw

variable {E : Type*} [Fintype E]

/-- Removing a subset of samples changes a bounded complex mean by at most
twice the bound times the removed fraction. -/
theorem finiteComplexMean_restriction_difference [Nonempty E]
    (A : E → Prop) [DecidablePred A] [Nonempty {e // A e}]
    (f : E → ℂ) (M : ℝ) (_hM : 0 ≤ M) (hf : ∀ e, ‖f e‖ ≤ M) :
    ‖finiteComplexMean f - finiteComplexMean (fun e : {e // A e} => f e.val)‖ ≤
      2 * M * (Nat.card {e // ¬A e} : ℝ) / (Fintype.card E : ℝ) := by
  classical
  let m := finiteComplexMean (fun e : {e // A e} => f e.val)
  have hm : ‖m‖ ≤ M := finiteComplexMean_norm_bound _ M (fun e => hf e.val)
  have hn : (Fintype.card E : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr Fintype.card_pos)
  have hA : (Fintype.card {e // A e} : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr Fintype.card_pos)
  have hzero : (∑ e : {e // A e}, (f e.val - m)) = 0 := by
    have hh := finiteComplexMean_sub_const (fun e : {e // A e} => f e.val) m
    change (Fintype.card {e // A e} : ℝ)⁻¹ • (∑ e : {e // A e}, (f e.val-m)) = m-m at hh
    rw [sub_self] at hh
    exact (smul_eq_zero.mp hh).resolve_left (inv_ne_zero hA)
  have hid : finiteComplexMean f - m =
      (Fintype.card E : ℝ)⁻¹ • (∑ e : {e // ¬A e}, (f e.val - m)) := by
    rw [← finiteComplexMean_sub_const f m]
    unfold finiteComplexMean
    have hsplit := Fintype.sum_subtype_add_sum_subtype A (fun e => f e-m)
    rw [← hsplit, hzero, zero_add]
  rw [hid, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ (Fintype.card E : ℝ)⁻¹ * (∑ _e : {e // ¬A e}, 2*M) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro e _
      exact (norm_sub_le _ _).trans (by linarith [hf e.val])
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Nat.card_eq_fintype_card]
      rw [div_eq_mul_inv]
      ring

/-- Two independent restricted draws incur two removed-density errors. No
assumption about independence of their endpoint values is used. -/
theorem finiteComplexMean_restriction_pair_difference [Nonempty E]
    (A : E → Prop) [DecidablePred A] [Nonempty {e // A e}]
    (f : E → E → ℂ) (M : ℝ) (hM : 0 ≤ M) (hf : ∀ e e', ‖f e e'‖ ≤ M) :
    ‖finiteComplexMean (fun e => finiteComplexMean (f e)) -
        finiteComplexMean (fun e : {e // A e} =>
          finiteComplexMean (fun e' : {e // A e} => f e.val e'.val))‖ ≤
      4 * M * (Nat.card {e // ¬A e} : ℝ) / (Fintype.card E : ℝ) := by
  let δ := 2 * M * (Nat.card {e // ¬A e} : ℝ) / (Fintype.card E : ℝ)
  let f1 : E → ℂ := fun e => finiteComplexMean (f e)
  let f2 : {e // A e} → ℂ := fun e => finiteComplexMean
    (fun e' : {e // A e} => f e.val e'.val)
  have hfirst : ‖finiteComplexMean f1 -
      finiteComplexMean (fun e : {e // A e} => f1 e.val)‖ ≤ δ := by
    apply finiteComplexMean_restriction_difference A f1 M hM
    intro e
    exact finiteComplexMean_norm_bound (f e) M (hf e)
  have hsecond : ‖finiteComplexMean (fun e : {e // A e} => f1 e.val) -
      finiteComplexMean f2‖ ≤ δ := by
    change ‖(Fintype.card {e // A e} : ℝ)⁻¹ • (∑ e : {e // A e}, f1 e.val) -
      (Fintype.card {e // A e} : ℝ)⁻¹ • (∑ e : {e // A e}, f2 e)‖ ≤ δ
    rw [← smul_sub, ← Finset.sum_sub_distrib]
    change ‖finiteComplexMean (fun e : {e // A e} => f1 e.val - f2 e)‖ ≤ δ
    apply finiteComplexMean_norm_bound
    intro e
    exact finiteComplexMean_restriction_difference A (f e.val) M hM (hf e.val)
  have htriangle := norm_add_le
    (finiteComplexMean f1 - finiteComplexMean (fun e : {e // A e} => f1 e.val))
    (finiteComplexMean (fun e : {e // A e} => f1 e.val) - finiteComplexMean f2)
  rw [sub_add_sub_cancel] at htriangle
  change ‖finiteComplexMean f1 - finiteComplexMean f2‖ ≤ _
  have heq : 4 * M * (Nat.card {e // ¬A e} : ℝ) / (Fintype.card E : ℝ) = 2*δ := by
    dsimp [δ]
    ring
  rw [heq]
  linarith

end SpectralConsequences
