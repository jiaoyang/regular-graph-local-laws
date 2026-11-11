import LocalLaw.ResamplingGeometricEvent
import LocalLaw.MomentTailParameters
import LocalLaw.SharpSamplingCounts
import LocalLaw.RadiusHierarchy
import LocalLaw.LocalSamplingAsymptotics
import LocalLaw.OffsetStructuralEvent

/-!
# Actual polynomial budgets for the source geometric sampling event

All four finite sampling terms have a positive power gap. One fixed common
count threshold, chosen from that gap, supplies every requested polynomial
failure exponent. Radius rounding and the actual boundary size are retained.
-/

open scoped BigOperators
namespace LocalLaw
noncomputable section
local instance geometricParameterDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- A finite logarithmic-density estimate with an explicit exponent gap. -/
theorem polylog_density_bound (N ℓ μ V A B α gap : ℝ) (m n : ℕ)
    (hN : 1 ≤ N) (hℓ : 1 ≤ ℓ) (_hμ : 0 ≤ μ) (hV : 0 ≤ V)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hμA : μ ≤ A * ℓ ^ m) (hVB : V ≤ B * N ^ α)
    (hmn : m ≤ n) (hgap : α + gap ≤ 1) :
    μ * V / N ≤ A * B * ℓ ^ n / N ^ gap := by
  have hn : 0 < N := by linarith
  have hpow := pow_le_pow_right₀ hℓ hmn
  have hprod : μ * V ≤ A * B * ℓ ^ n * N ^ α := by
    calc
      _ ≤ (A * ℓ ^ m) * (B * N ^ α) := mul_le_mul hμA hVB hV (by positivity)
      _ = A * B * ℓ ^ m * N ^ α := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (mul_nonneg hA hB))
        (Real.rpow_nonneg hn.le _)
  have hNg : N ^ α * N ^ gap ≤ N := by
    rw [← Real.rpow_add hn]
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN hgap
  apply (div_le_div_iff₀ hn (Real.rpow_pos_of_pos hn gap)).mpr
  calc
    _ ≤ (A * B * ℓ ^ n * N ^ α) * N ^ gap :=
      mul_le_mul_of_nonneg_right hprod (Real.rpow_nonneg hn.le _)
    _ = (A * B * ℓ ^ n) * (N ^ α * N ^ gap) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hNg (by positivity)

def geometricSamplingConstant (d : ℕ) : ℝ :=
  let M := (d : ℝ) * ((d : ℝ) + 1)
  4 * M * ((d : ℝ) + 1) + 8 * M ^ 2 * ((d : ℝ) + 1) + 4 * M

/-- All four bases in the finite F1 estimate share one polylogarithmic budget. -/
theorem geometric_sampling_bases (N ℓ μ V b : ℝ) (a d : ℕ) (c γ gap : ℝ)
    (hN : 1 ≤ N) (hℓ : 1 ≤ ℓ) (hμ : 0 ≤ μ) (hV : 0 ≤ V) (hb : 0 ≤ b)
    (hμbound : μ ≤ (d : ℝ) * ((d : ℝ) + 1) * ℓ ^ (2 * a))
    (hVbound : V ≤ ((d : ℝ) + 1) * N ^ (c / 4)) (hbbound : b ≤ N ^ γ)
    (hgapc : c / 4 + gap ≤ 1) (hgapγ : γ + gap ≤ 1) :
    let A := geometricSamplingConstant d * ℓ ^ (4 * a) / N ^ gap
    μ * (4 * V / N) ≤ A ∧ 4 * μ ^ 2 * V / N ≤ A ∧
      μ ^ 2 * (8 * V / N) ≤ A ∧ μ * (4 * b / N) ≤ A := by
  let M := (d : ℝ) * ((d : ℝ) + 1)
  let C := geometricSamplingConstant d
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hC₁ : M * (4 * ((d : ℝ) + 1)) ≤ C := by
    dsimp [C, geometricSamplingConstant]
    change M * (4 * ((d : ℝ) + 1)) ≤ 4 * M * ((d : ℝ) + 1) + 8 * M ^ 2 * ((d : ℝ) + 1) + 4 * M
    nlinarith [mul_nonneg (sq_nonneg M) (show 0 ≤ (d : ℝ) + 1 by positivity)]
  have hC₂ : M ^ 2 * (4 * ((d : ℝ) + 1)) ≤ C := by
    dsimp [C, geometricSamplingConstant]
    change M ^ 2 * (4 * ((d : ℝ) + 1)) ≤ 4 * M * ((d : ℝ) + 1) + 8 * M ^ 2 * ((d : ℝ) + 1) + 4 * M
    nlinarith [mul_nonneg (sq_nonneg M) (show 0 ≤ (d : ℝ) + 1 by positivity)]
  have hC₃ : M ^ 2 * (8 * ((d : ℝ) + 1)) ≤ C := by
    dsimp [C, geometricSamplingConstant]
    change M ^ 2 * (8 * ((d : ℝ) + 1)) ≤ 4 * M * ((d : ℝ) + 1) + 8 * M ^ 2 * ((d : ℝ) + 1) + 4 * M
    nlinarith [mul_nonneg hM (show 0 ≤ (d : ℝ) + 1 by positivity)]
  have hC₄ : M * 4 ≤ C := by
    dsimp [C, geometricSamplingConstant]
    change M * 4 ≤ 4 * M * ((d : ℝ) + 1) + 8 * M ^ 2 * ((d : ℝ) + 1) + 4 * M
    nlinarith [mul_nonneg hM (show 0 ≤ (d : ℝ) + 1 by positivity),
      mul_nonneg (sq_nonneg M) (show 0 ≤ (d : ℝ) + 1 by positivity)]
  have hμ₂ : μ ^ 2 ≤ M ^ 2 * ℓ ^ (4 * a) := by
    have hh : μ ^ 2 ≤ (M * ℓ ^ (2 * a)) ^ 2 := pow_le_pow_left₀ hμ hμbound 2
    have heq : (M * ℓ ^ (2 * a)) ^ 2 = M ^ 2 * ℓ ^ (4 * a) := by
      rw [mul_pow, ← pow_mul, show 2 * a * 2 = 4 * a by omega]
    rw [heq] at hh
    exact hh
  have hcoef : ∀ A : ℝ, A ≤ C → A * ℓ ^ (4 * a) / N ^ gap ≤ C * ℓ ^ (4 * a) / N ^ gap := by
    intro A hA
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hA (by positivity)) (Real.rpow_nonneg (by linarith) _)
  have h₁ := polylog_density_bound N ℓ μ (4 * V) M (4 * ((d : ℝ) + 1)) (c / 4) gap
    (2 * a) (4 * a) hN hℓ hμ (by positivity) hM (by positivity) hμbound
    (by nlinarith) (by omega) hgapc
  have h₂ := polylog_density_bound N ℓ (μ ^ 2) (4 * V) (M ^ 2) (4 * ((d : ℝ) + 1)) (c / 4) gap
    (4 * a) (4 * a) hN hℓ (sq_nonneg _) (by positivity) (sq_nonneg _) (by positivity) hμ₂
    (by nlinarith) le_rfl hgapc
  have h₃ := polylog_density_bound N ℓ (μ ^ 2) (8 * V) (M ^ 2) (8 * ((d : ℝ) + 1)) (c / 4) gap
    (4 * a) (4 * a) hN hℓ (sq_nonneg _) (by positivity) (sq_nonneg _) (by positivity) hμ₂
    (by nlinarith) le_rfl hgapc
  have h₄ := polylog_density_bound N ℓ μ (4 * b) M 4 γ gap
    (2 * a) (4 * a) hN hℓ hμ (by positivity) hM (by norm_num) hμbound
    (by nlinarith) (by omega) hgapγ
  refine ⟨?_, ?_, ?_, ?_⟩
  · convert h₁.trans (hcoef _ hC₁) using 1
    ring
  · convert h₂.trans (hcoef _ hC₂) using 1
    ring
  · convert h₃.trans (hcoef _ hC₃) using 1
    ring
  · convert h₄.trans (hcoef _ hC₄) using 1
    ring

/-- One fixed common count threshold makes the actual four finite probability
terms smaller than four times every prescribed polynomial budget. -/
theorem eventually_geometric_sampling_budget (a d p : ℕ) (c γ : ℝ)
    (hc : c < 1) (hγ : γ < 1) :
    ∃ q : ℕ, 1 ≤ q ∧ ∀ᶠ N : ℕ in Filter.atTop, ∀ μ V b : ℝ,
      0 ≤ μ → 0 ≤ V → 0 ≤ b →
      μ ≤ (d : ℝ) * ((d : ℝ) + 1) * Real.log (N : ℝ) ^ (2 * a) →
      V ≤ ((d : ℝ) + 1) * (N : ℝ) ^ (c / 4) → b ≤ (N : ℝ) ^ γ →
      2 * (N : ℝ) * (μ * (4 * V / N)) ^ q + (4 * μ ^ 2 * V / N) ^ q +
        (μ ^ 2 * (8 * V / N)) ^ q + (μ * (4 * b / N)) ^ q ≤ 4 / (N : ℝ) ^ p := by
  let gap := min (1 - c / 4) (1 - γ)
  let C := geometricSamplingConstant d
  let q := sufficientMomentOrder gap (p + 1)
  have hgap : 0 < gap := by
    dsimp only [gap]
    exact lt_min (by linarith) (by linarith)
  have hqbound := sufficientMomentOrder_bound gap (p + 1) hgap
  have hq : 1 ≤ q := by
    by_contra hnot
    have hzero : q = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (Nat.lt_of_not_ge hnot))
    change ((p + 1 + 1 : ℕ) : ℝ) ≤ (q : ℝ) * gap / 2 at hqbound
    rw [hzero] at hqbound
    norm_num at hqbound
    linarith
  have hC : 0 ≤ C := by dsimp [C, geometricSamplingConstant]; positivity
  refine ⟨q, hq, ?_⟩
  filter_upwards [eventually_chosen_moment_decay C gap (4 * a) (p + 1) hC hgap,
    eventually_log_ge_nat 1, Filter.eventually_ge_atTop 1] with N htail hlog hN
  intro μ V b hμ hV hb hμbound hVbound hbbound
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hn₁ : (1 : ℝ) ≤ N := by exact_mod_cast hN
  let A := C * Real.log (N : ℝ) ^ (4 * a) / (N : ℝ) ^ gap
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hbases := geometric_sampling_bases (N : ℝ) (Real.log (N : ℝ)) μ V b a d c γ gap
    hn₁ hlog hμ hV hb hμbound hVbound hbbound
    (by have hh := min_le_left (1 - c / 4) (1 - γ); change gap ≤ _ at hh; linarith)
    (by have hh := min_le_right (1 - c / 4) (1 - γ); change gap ≤ _ at hh; linarith)
  change _ ≤ A ∧ _ ≤ A ∧ _ ≤ A ∧ _ ≤ A at hbases
  have hp₁ := pow_le_pow_left₀ (show 0 ≤ μ * (4 * V / N) by positivity) hbases.1 q
  have hp₂ := pow_le_pow_left₀ (show 0 ≤ 4 * μ ^ 2 * V / N by positivity) hbases.2.1 q
  have hp₃ := pow_le_pow_left₀ (show 0 ≤ μ ^ 2 * (8 * V / N) by positivity) hbases.2.2.1 q
  have hp₄ := pow_le_pow_left₀ (show 0 ≤ μ * (4 * b / N) by positivity) hbases.2.2.2 q
  change 2 * A ^ q ≤ 1 / (N : ℝ) ^ (p + 1) at htail
  have hden : 1 / (N : ℝ) ^ (p + 1) ≤ 1 / (N : ℝ) ^ p :=
    one_div_le_one_div_of_le (pow_pos hn _) (pow_le_pow_right₀ hn₁ (by omega))
  have hrest : A ^ q ≤ 1 / (N : ℝ) ^ p := by
    have hh : A ^ q ≤ 2 * A ^ q := by nlinarith [pow_nonneg hA q]
    exact hh.trans (htail.trans hden)
  have hfirst : 2 * (N : ℝ) * (μ * (4 * V / N)) ^ q ≤ 1 / (N : ℝ) ^ p := by
    have hh := mul_le_mul_of_nonneg_left htail hn.le
    have heq : (N : ℝ) * (1 / (N : ℝ) ^ (p + 1)) = 1 / (N : ℝ) ^ p := by
      rw [pow_succ]; field_simp; ring
    rw [heq] at hh
    nlinarith [mul_le_mul_of_nonneg_left hp₁ hn.le]
  have hsum := add_le_add (add_le_add (add_le_add hfirst (hp₂.trans hrest)) (hp₃.trans hrest)) (hp₄.trans hrest)
  convert hsum using 1
  ring

namespace RegularGraph

/-- The finite F1 count estimate and all actual radius/count budgets give
uniform arbitrary polynomial failure on the offset auxiliary event. -/
theorem eventually_sourceGeometricGood_probability (a d ω p : ℕ) (c γ : ℝ)
    (hd : 3 ≤ d) (hc : 0 < c) (hc₁ : c < 1) (hγ : γ < 1) :
    ∃ q : ℕ, 1 ≤ q ∧ ∀ᶠ N : ℕ in Filter.atTop,
      ∀ (g : RegularGraph N d) (o : Fin N) (ell : ℕ), ell ≤ doubleLogRadius a d N →
      graphBallExcess g.graph o (logarithmicRadius (c / 4) d N) ≤ ω →
      (nonTreeCenters g.graph (logarithmicRadius (c / 4) d N + 1)).card ≤ ⌊(N : ℝ) ^ γ⌋₊ →
      eventMass (localSamplingWeight g.graph (graphBallVertices g.graph o ell))
        (fun S => ¬ SourceGeometricGood g.graph o ell (logarithmicRadius (c / 4) d N) ω
          (q - 1) (q - 1) (2 * q * (2 * (q - 1) + 1)) (q - 1) S) ≤
        4 / (N : ℝ) ^ p := by
  obtain ⟨q, hq, hnum⟩ := eventually_geometric_sampling_budget a d p c γ hc₁ hγ
  refine ⟨q, hq, ?_⟩
  filter_upwards [hnum, eventually_resampling_ball_budget a d hd,
    eventually_resampling_radius_margin a d 2 2 (c / 4) hd (by linarith),
    eventually_log_ge_nat 1, Filter.eventually_ge_atTop 1] with N hnum hball hmargin hlog hN
  intro g o ell hell hexcess hbad
  let R := logarithmicRadius (c / 4) d N
  let μ : ℝ := Nat.card (BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
  let V : ℝ := (((d + 1) * (d - 1) ^ R : ℕ) : ℝ)
  let b : ℕ := ⌊(N : ℝ) ^ γ⌋₊
  have hT : 4 * Nat.card (graphBallVertices g.graph o ell) ≤ N := by
    apply (Nat.mul_le_mul_left 4 ((g.ball_card_bound o ell).trans
      (Nat.pow_le_pow_right (by omega : 0 < d + 1) hell))).trans hball
  have hmargin' : 2 * ell + 2 ≤ R := by dsimp only [R]; omega
  have hμ : μ ≤ (d : ℝ) * ((d : ℝ) + 1) * Real.log (N : ℝ) ^ (2 * a) :=
    g.boundary_card_log_bound o a ell hd hlog hell
  have hV : V ≤ ((d : ℝ) + 1) * (N : ℝ) ^ (c / 4) := by
    have hh := logarithmicRadius_power_bound (c / 4) d N (by linarith) hd hN
    dsimp only [V, R]
    push_cast
    exact mul_le_mul_of_nonneg_left hh (by positivity)
  have hb : (b : ℝ) ≤ (N : ℝ) ^ γ := Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) γ)
  have hprob := g.localSampling_sourceGeometricGood_failure o ell R ω (q - 1) (q - 1) q (q - 1) b
    (by omega) hd hT hmargin' hexcess hbad
  have hexp : q - 1 + 1 = q := Nat.sub_add_cancel hq
  rw [hexp] at hprob
  exact hprob.trans (hnum μ V (b : ℝ) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) hμ hV hb)

/-- The chosen nonresonant source radius also realizes the same count bound
on the actual offset auxiliary event; its radius comparison is derived. -/
theorem eventually_selected_sourceGeometricGood_probability (a d ω p : ℕ) (c γ : ℝ)
    (ha : 0 < a) (hd : 3 ≤ d) (hc : 0 < c) (hc₁ : c < 1) (hγ : γ < 1) :
    ∃ q : ℕ, 1 ≤ q ∧ ∀ᶠ N : ℕ in Filter.atTop,
      ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      offsetStructural (logarithmicRadius (c / 4) d N) ω 1 ⌊(N : ℝ) ^ γ⌋₊ g →
      eventMass (localSamplingWeight g.graph
        (graphBallVertices g.graph o (actualCavityDepth a d N z - 1)))
        (fun S => ¬ SourceGeometricGood g.graph o (actualCavityDepth a d N z - 1)
          (logarithmicRadius (c / 4) d N) ω (q - 1) (q - 1)
          (2 * q * (2 * (q - 1) + 1)) (q - 1) S) ≤ 4 / (N : ℝ) ^ p := by
  obtain ⟨q, hq, hprob⟩ := eventually_sourceGeometricGood_probability a d ω p c γ hd hc hc₁ hγ
  have hr := (lowerLogLogRadius_tendsto a d ha hd).eventually (Filter.eventually_ge_atTop 4)
  refine ⟨q, hq, ?_⟩
  filter_upwards [hprob, hr] with N hprob hr
  intro g o z haux
  exact hprob g o _ (actualCavityDepth_radius_bounds a d N z hr).2 (haux.1 o) haux.2

end RegularGraph

end
end LocalLaw
