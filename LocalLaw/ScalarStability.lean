import Mathlib

/-!
# Scalar stability for a local-law bootstrap

A small quadratic residual is converted to improved control of the selected
root. The separated branch uses the a priori estimate; the near-edge branch
uses quadratic coercivity. All constants and positivity assumptions are explicit.
-/

namespace LocalLaw

/-- The error scale at a regular square-root spectral edge. -/
noncomputable def scalarScale (s ε : ℝ) : ℝ := ε / Real.sqrt (s + ε)

lemma scalarScale_nonneg {s ε : ℝ} (hε : 0 ≤ ε) : 0 ≤ scalarScale s ε := by
  exact div_nonneg hε (Real.sqrt_nonneg _)

lemma scalarScale_le_sqrt {s ε : ℝ} (hs : 0 < s) (hε : 0 ≤ ε) :
    scalarScale s ε ≤ Real.sqrt ε := by
  have hr : 0 < Real.sqrt (s + ε) := Real.sqrt_pos.2 (by linarith)
  unfold scalarScale
  apply (div_le_iff₀ hr).2
  have hcomp : Real.sqrt ε ≤ Real.sqrt (s + ε) :=
    Real.sqrt_le_sqrt (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hcomp (Real.sqrt_nonneg ε)
  nlinarith [Real.mul_self_sqrt hε]

lemma scalarScale_sqrt_mul_le {s ε : ℝ} (hs : 0 < s) (hε : 0 ≤ ε) :
    Real.sqrt s * scalarScale s ε ≤ ε := by
  have hr : 0 < Real.sqrt (s + ε) := Real.sqrt_pos.2 (by linarith)
  unfold scalarScale
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hr).2
  have hcomp : Real.sqrt s ≤ Real.sqrt (s + ε) :=
    Real.sqrt_le_sqrt (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left hcomp hε]

lemma scalarScale_sq_le {s ε : ℝ} (hs : 0 < s) (hε : 0 ≤ ε) :
    scalarScale s ε ^ 2 ≤ ε := by
  have h₁ := scalarScale_nonneg (s := s) hε
  have h₂ := scalarScale_le_sqrt hs hε
  nlinarith [Real.sq_sqrt hε]

/-- Root separation turns the residual into a linear bound. -/
theorem scalar_norm_stable (δ g : ℂ) (R : ℝ)
    (hsmall : ‖δ‖ ≤ ‖g‖ / 2) (hres : ‖δ * (δ - g)‖ ≤ R) :
    ‖δ‖ * ‖g‖ ≤ 2 * R := by
  rw [norm_mul] at hres
  have hrev : ‖g‖ - ‖δ‖ ≤ ‖δ - g‖ := by
    simpa only [norm_sub_rev] using norm_sub_norm_le g δ
  have hmul := mul_le_mul_of_nonneg_left hrev (norm_nonneg δ)
  have hδ := norm_nonneg δ
  nlinarith

/-- A real quadratic inequality, with no choice of complex square root. -/
lemma quadratic_norm_bound {u v R : ℝ} (_hu : 0 ≤ u) (hv : 0 ≤ v)
    (hR : 0 ≤ R) (hquad : u ^ 2 ≤ v * u + R) :
    u ≤ v + Real.sqrt R := by
  by_contra h
  have hlt : v + Real.sqrt R < u := lt_of_not_ge h
  have hut : Real.sqrt R < u := by linarith
  have hdiff : Real.sqrt R < u - v := by linarith
  have hup : 0 < u := lt_of_le_of_lt (Real.sqrt_nonneg R) hut
  have hprod : Real.sqrt R * Real.sqrt R < u * (u - v) :=
    lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right hut.le (Real.sqrt_nonneg R))
      (mul_lt_mul_of_pos_left hdiff hup)
  nlinarith [Real.mul_self_sqrt hR]

/-- Quadratic coercivity remains valid when the two roots nearly meet. -/
theorem scalar_norm_edge (δ g : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hres : ‖δ * (δ - g)‖ ≤ R) :
    ‖δ‖ ≤ ‖g‖ + Real.sqrt R := by
  rw [norm_mul] at hres
  have hrev : ‖δ‖ - ‖g‖ ≤ ‖δ - g‖ := norm_sub_norm_le δ g
  have hmul := mul_le_mul_of_nonneg_left hrev (norm_nonneg δ)
  apply quadratic_norm_bound (norm_nonneg δ) (norm_nonneg g) hR
  nlinarith

/-- In the separated regime the a priori bound excludes the other root. -/
theorem scalar_prior_separates (δ g : ℂ) (s ε L K : ℝ)
    (hs : 0 < s) (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (hL : 0 < L) (hLK : 2 * K ≤ L)
    (hgap : Real.sqrt s ≤ ‖g‖)
    (hprior : ‖δ‖ ≤ K * scalarScale s ε)
    (hreg : ε ≤ s / L) :
    ‖δ‖ ≤ ‖g‖ / 2 := by
  have hr : 0 < Real.sqrt (s + ε) := Real.sqrt_pos.2 (by linarith)
  have hrs : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hcomp : Real.sqrt s ≤ Real.sqrt (s + ε) :=
    Real.sqrt_le_sqrt (by linarith)
  have hp : ‖δ‖ * Real.sqrt (s + ε) ≤ K * ε := by
    apply (le_div_iff₀ hr).1
    simpa only [scalarScale, mul_div_assoc] using hprior
  have he : ε * L ≤ s := (le_div_iff₀ hL).1 hreg
  have hpl := mul_le_mul_of_nonneg_right hp hL.le
  have heK := mul_le_mul_of_nonneg_left he hK
  have hcmp := mul_le_mul_of_nonneg_left hcomp
    (show 0 ≤ ‖δ‖ * L by positivity)
  have hlinear : ‖δ‖ * L ≤ K * Real.sqrt s := by
    apply (mul_le_mul_right hrs).1
    nlinarith [Real.sq_sqrt hs.le]
  have hKmul := mul_le_mul_of_nonneg_right hLK (Real.sqrt_nonneg s)
  have htwice : ‖δ‖ * 2 ≤ Real.sqrt s := by
    apply (mul_le_mul_right hL).1
    nlinarith
  linarith

/-- A conservative rational-constant version of the separated improvement. -/
theorem scalar_separated_bound (δ g : ℂ) (s ε L K M : ℝ)
    (hs : 0 < s) (hε : 0 ≤ ε) (hK : 0 ≤ K) (_hM : 0 ≤ M)
    (hL : 2 ≤ L) (hLK : 2 * K ≤ L)
    (hgap : Real.sqrt s ≤ ‖g‖)
    (hprior : ‖δ‖ ≤ K * scalarScale s ε)
    (hres : ‖δ * (δ - g)‖ ≤ M * ε / L ^ 2)
    (hreg : ε ≤ s / L) :
    ‖δ‖ ≤ 4 * M * scalarScale s ε / L ^ 2 := by
  have hLp : 0 < L := by linarith
  have hLsq : 0 < L ^ 2 := sq_pos_of_pos hLp
  have hr : 0 < Real.sqrt (s + ε) := Real.sqrt_pos.2 (by linarith)
  have hsmall := scalar_prior_separates δ g s ε L K hs hε hK hLp hLK
    hgap hprior hreg
  have hstable := scalar_norm_stable δ g (M * ε / L ^ 2) hsmall hres
  have hεs : ε ≤ s := by
    have := (le_div_iff₀ hLp).1 hreg
    nlinarith
  have hroot : Real.sqrt (s + ε) ≤ 2 * Real.sqrt s := by
    nlinarith [Real.sq_sqrt (show 0 ≤ s + ε by linarith),
      Real.sq_sqrt hs.le, Real.sqrt_nonneg (s + ε), Real.sqrt_nonneg s]
  have hlin : ‖δ‖ * Real.sqrt s ≤ 2 * (M * ε / L ^ 2) :=
    (mul_le_mul_of_nonneg_left hgap (norm_nonneg δ)).trans hstable
  have hlin' : ‖δ‖ * Real.sqrt s * L ^ 2 ≤ 2 * M * ε := by
    have := (le_div_iff₀ hLsq).1 (show
      ‖δ‖ * Real.sqrt s ≤ (2 * M * ε) / L ^ 2 by
        simpa only [mul_div_assoc, mul_assoc] using hlin)
    exact this
  unfold scalarScale
  apply (le_div_iff₀ hLsq).2
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hr).2
  have hcmp := mul_le_mul_of_nonneg_left hroot
    (show 0 ≤ ‖δ‖ * L ^ 2 by positivity)
  nlinarith

/-- The near-edge regime has a uniform bound even without the a priori branch condition. -/
theorem scalar_edge_bound (δ g : ℂ) (s ε L G M : ℝ)
    (hs : 0 < s) (hε : 0 < ε) (hG : 0 ≤ G) (hM : 0 ≤ M)
    (hL : 2 ≤ L) (hgap : ‖g‖ ≤ G * Real.sqrt s)
    (hres : ‖δ * (δ - g)‖ ≤ M * ε / L ^ 2)
    (hreg : L ^ 3 * s ≤ ε) :
    ‖δ‖ ≤ 2 * (G + Real.sqrt M) * scalarScale s ε / L := by
  have hLp : 0 < L := by linarith
  have hLsq : 0 < L ^ 2 := sq_pos_of_pos hLp
  have hR : 0 ≤ M * ε / L ^ 2 := by positivity
  have hgeneric := scalar_norm_edge δ g (M * ε / L ^ 2) hR hres
  have hsqrt : Real.sqrt (M * ε / L ^ 2) =
      Real.sqrt M * Real.sqrt ε / L := by
    rw [Real.sqrt_div (mul_nonneg hM hε.le), Real.sqrt_mul hM,
      Real.sqrt_sq_eq_abs, abs_of_pos hLp]
  have hL23 : L ^ 2 ≤ L ^ 3 := by nlinarith [sq_nonneg L]
  have hsq : L ^ 2 * s ≤ ε :=
    (mul_le_mul_of_nonneg_right hL23 hs.le).trans hreg
  have hroots : L * Real.sqrt s ≤ Real.sqrt ε := by
    have := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_mul (sq_nonneg L), Real.sqrt_sq_eq_abs, abs_of_pos hLp] at this
  have hsε : s ≤ ε := by nlinarith [mul_le_mul_of_nonneg_right hL23 hs.le]
  have hroot : Real.sqrt (s + ε) ≤ 2 * Real.sqrt ε := by
    nlinarith [Real.sq_sqrt (show 0 ≤ s + ε by linarith),
      Real.sq_sqrt hε.le, Real.sqrt_nonneg (s + ε), Real.sqrt_nonneg ε]
  have hlin : ‖δ‖ ≤ (G + Real.sqrt M) * Real.sqrt ε / L := by
    rw [hsqrt] at hgeneric
    have hgap' : ‖g‖ * L ≤ G * Real.sqrt ε := by
      nlinarith [mul_le_mul_of_nonneg_left hroots hG]
    apply (le_div_iff₀ hLp).2
    have hh := mul_le_mul_of_nonneg_right hgeneric hLp.le
    have hc : (Real.sqrt M * Real.sqrt ε / L) * L =
        Real.sqrt M * Real.sqrt ε := div_mul_cancel₀ _ (ne_of_gt hLp)
    nlinarith
  have hr : 0 < Real.sqrt (s + ε) := Real.sqrt_pos.2 (by linarith)
  have hscl : Real.sqrt ε ≤ 2 * scalarScale s ε := by
    unfold scalarScale
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hr).2
    nlinarith [mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg ε),
      Real.sq_sqrt hε.le]
  have hcoef : 0 ≤ G + Real.sqrt M := by positivity
  calc
    ‖δ‖ ≤ (G + Real.sqrt M) * Real.sqrt ε / L := hlin
    _ ≤ (G + Real.sqrt M) * (2 * scalarScale s ε) / L :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hscl hcoef) hLp.le
    _ = 2 * (G + Real.sqrt M) * scalarScale s ε / L := by ring

/-- One explicit constant controlling both scalar regimes. -/
noncomputable def scalarConstant (G M : ℝ) : ℝ :=
  max 1 (max (4 * M) (2 * (G + Real.sqrt M)))

lemma scalarConstant_one_le (G M : ℝ) : 1 ≤ scalarConstant G M :=
  le_max_left _ _

lemma scalarConstant_stable_le (G M : ℝ) : 4 * M ≤ scalarConstant G M :=
  (le_max_left _ _).trans (le_max_right _ _)

lemma scalarConstant_edge_le (G M : ℝ) :
    2 * (G + Real.sqrt M) ≤ scalarConstant G M :=
  (le_max_right _ _).trans (le_max_right _ _)

lemma scalarScale_mul_sqrt_le {s ε : ℝ} (hs : 0 < s) (hε : 0 ≤ ε) :
    scalarScale s ε * Real.sqrt ε ≤ ε := by
  have h := mul_le_mul_of_nonneg_right (scalarScale_le_sqrt hs hε)
    (Real.sqrt_nonneg ε)
  nlinarith [Real.mul_self_sqrt hε]

/-- An algebraic feedback lemma used after the branch estimates. -/
lemma scalar_feedback_of_linear (δ : ℂ) (s ε L C : ℝ)
    (hs : 0 < s) (hε : 0 ≤ ε) (hL : 0 < L) (_hC : 0 ≤ C)
    (hscale : ‖δ‖ * L ≤ C * scalarScale s ε)
    (hlinear : L ^ 2 * Real.sqrt s * ‖δ‖ ≤ C * ε) :
    L * (Real.sqrt s * ‖δ‖ + ‖δ‖ ^ 2) ≤ (C + C ^ 2) * ε / L := by
  have hsq₁ := mul_self_le_mul_self (show 0 ≤ ‖δ‖ * L by positivity) hscale
  have hsq₂ := mul_le_mul_of_nonneg_left (scalarScale_sq_le hs hε) (sq_nonneg C)
  have hquadratic : L ^ 2 * ‖δ‖ ^ 2 ≤ C ^ 2 * ε := by nlinarith
  apply (le_div_iff₀ hL).2
  nlinarith

/-- Quantitative two-regime stability and the feedback estimate required
by the local-law bootstrap. The constants are conservative rational enlargements
of the sharp constants in the mathematical blueprint. -/
theorem scalar_two_regime (δ g : ℂ) (s ε L K G M : ℝ)
    (hs : 0 < s) (hε : 0 < ε) (hK : 0 ≤ K) (hG : 0 ≤ G) (hM : 0 ≤ M)
    (hL : 2 ≤ L) (hLK : 2 * K ≤ L)
    (hgap₁ : Real.sqrt s ≤ ‖g‖) (hgap₂ : ‖g‖ ≤ G * Real.sqrt s)
    (hprior : ‖δ‖ ≤ K * scalarScale s ε)
    (hres : ‖δ * (δ - g)‖ ≤ M * ε / L ^ 2)
    (hreg : ε ≤ s / L ∨ L ^ 3 * s ≤ ε) :
    ‖δ‖ ≤ scalarConstant G M * scalarScale s ε / L ∧
    L * (Real.sqrt s * ‖δ‖ + ‖δ‖ ^ 2) ≤
      (scalarConstant G M + scalarConstant G M ^ 2) * ε / L := by
  let C := scalarConstant G M
  have hC : 0 ≤ C := by dsimp [C]; linarith [scalarConstant_one_le G M]
  have hLp : 0 < L := by linarith
  have hLsq : 0 < L ^ 2 := sq_pos_of_pos hLp
  have hΨ : 0 ≤ scalarScale s ε := scalarScale_nonneg hε.le
  have hlinear_and_scale :
      ‖δ‖ * L ≤ C * scalarScale s ε ∧
      L ^ 2 * Real.sqrt s * ‖δ‖ ≤ C * ε := by
    rcases hreg with hlow | hedge
    · have hbound := scalar_separated_bound δ g s ε L K M hs hε.le hK hM
        hL hLK hgap₁ hprior hres hlow
      have hboundC : ‖δ‖ ≤ C * scalarScale s ε / L ^ 2 := by
        exact hbound.trans (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (scalarConstant_stable_le G M) hΨ)
          (sq_nonneg L))
      have huL2 := (le_div_iff₀ hLsq).1 hboundC
      have hLL : L ≤ L ^ 2 := by nlinarith
      have huL : ‖δ‖ * L ≤ C * scalarScale s ε :=
        (mul_le_mul_of_nonneg_left hLL (norm_nonneg δ)).trans huL2
      refine ⟨huL, ?_⟩
      calc
        L ^ 2 * Real.sqrt s * ‖δ‖ = (‖δ‖ * L ^ 2) * Real.sqrt s := by ring
        _ ≤ (C * scalarScale s ε) * Real.sqrt s :=
          mul_le_mul_of_nonneg_right huL2 (Real.sqrt_nonneg s)
        _ = C * (Real.sqrt s * scalarScale s ε) := by ring
        _ ≤ C * ε := mul_le_mul_of_nonneg_left (scalarScale_sqrt_mul_le hs hε.le) hC
    · have hbound := scalar_edge_bound δ g s ε L G M hs hε hG hM
        hL hgap₂ hres hedge
      have hboundC : ‖δ‖ ≤ C * scalarScale s ε / L := by
        exact hbound.trans (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (scalarConstant_edge_le G M) hΨ) hLp.le)
      have huL := (le_div_iff₀ hLp).1 hboundC
      have hL23 : L ^ 2 ≤ L ^ 3 := by nlinarith [sq_nonneg L]
      have hsq : L ^ 2 * s ≤ ε :=
        (mul_le_mul_of_nonneg_right hL23 hs.le).trans hedge
      have hroots : L * Real.sqrt s ≤ Real.sqrt ε := by
        have := Real.sqrt_le_sqrt hsq
        rwa [Real.sqrt_mul (sq_nonneg L), Real.sqrt_sq_eq_abs, abs_of_pos hLp] at this
      refine ⟨huL, ?_⟩
      calc
        L ^ 2 * Real.sqrt s * ‖δ‖ = (‖δ‖ * L) * (L * Real.sqrt s) := by ring
        _ ≤ (C * scalarScale s ε) * (L * Real.sqrt s) :=
          mul_le_mul_of_nonneg_right huL (by positivity)
        _ ≤ (C * scalarScale s ε) * Real.sqrt ε :=
          mul_le_mul_of_nonneg_left hroots (mul_nonneg hC hΨ)
        _ = C * (scalarScale s ε * Real.sqrt ε) := by ring
        _ ≤ C * ε := mul_le_mul_of_nonneg_left (scalarScale_mul_sqrt_le hs hε.le) hC
  refine ⟨(le_div_iff₀ hLp).2 hlinear_and_scale.1, ?_⟩
  exact scalar_feedback_of_linear δ s ε L C hs hε.le hLp hC
    hlinear_and_scale.1 hlinear_and_scale.2

end LocalLaw
