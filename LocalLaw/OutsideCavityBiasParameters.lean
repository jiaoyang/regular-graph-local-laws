import LocalLaw.OutsideCavityMean

/-!
# Actual one-edge cavity expectation versus Q

Both the physical principal-deletion cost and the exact outside-edge
normalization change are absorbed at the source logarithmic radii. This is
the Q part of the bias estimate in the unswitched concentration argument.
-/

namespace LocalLaw
noncomputable section
local instance outsideCavityBiasParameterDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem deletion_density_ward_budget (N t : ℕ) (B M η : ℝ) (hN : 0 < N)
    (hM : 0 ≤ M) (hη : 0 < η) (hηB : η ≤ B) :
    (2 * (t : ℝ) / (N : ℝ)) * M ≤ (2 * B * M) * (t : ℝ) ^ 2 / ((N : ℝ) * η) := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have ht : (t : ℝ) ≤ (t : ℝ) ^ 2 := by
    have hh : (t : ℝ) ≤ (t : ℝ) * (t : ℝ) := by exact_mod_cast Nat.le_mul_self t
    simpa only [pow_two] using hh
  apply (le_div_iff₀ (mul_pos hn hη)).mpr
  have heq : ((2 * (t : ℝ) / (N : ℝ)) * M) * ((N : ℝ) * η) = 2 * (t : ℝ) * M * η := by
    field_simp
    ring
  rw [heq]
  calc
    _ ≤ 2 * (t : ℝ) ^ 2 * M * B := by gcongr
    _ = _ := by ring

namespace RegularGraph

/-- The genuine finite one-edge mean differs from actual Q by at most two
sixteen-logarithm tolerances. All counting, normalization and Schur/Ward
estimates are conclusions, with physical Green/pivot caps kept explicit. -/
theorem eventually_ball_outside_cavity_mean_bias_small (a b d : ℕ) (B C L : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hL : 0 ≤ L) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (ell r : ℕ) (z : ℂ),
      ell ≤ doubleLogRadius a d N → 0 < z.im → ‖z‖ ≤ B →
      Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
      (∀ i j, ‖g.G z i j‖ ≤ C) → (∀ j, ‖(g.G z j j)⁻¹‖ ≤ L) →
      (∀ i j, ‖green (normalizedAdjacency (outsideGraph g.graph (graphBallVertices g.graph o ell)) d) z i j‖ ≤ C) →
      (∀ j, ‖(green (normalizedAdjacency (outsideGraph g.graph (graphBallVertices g.graph o ell)) d) z j j)⁻¹‖ ≤ L) →
      ‖g.Q z - finiteComplexMean (outsideOrientedCavityValue g.graph d (graphBallVertices g.graph o ell) z)‖ ≤
        2 * graphPaperError a d N r z / Real.log (N : ℝ) ^ 16 := by
  let M := C + C ^ 2 * L
  let K := 2 * B * M
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  filter_upwards [eventually_ball_Q_outside_cavity_bias_small a b d B C L ha hb hd hB hC hL,
    eventually_resampling_ball_budget a d hd, eventually_log_ge_nat 1,
    eventually_log_ge_nat (K * ((d : ℝ) + 1) ^ 2), Filter.eventually_ge_atTop 1]
    with N hraw hball hlog hmargin hN
  intro g o ell r z hell hz hzB hscale hR hRi hS hSi
  let T := graphBallVertices g.graph o ell
  let f := outsideOrientedCavityValue g.graph d T z
  have hT : 4 * Nat.card T ≤ N := by
    apply (Nat.mul_le_mul_left 4 ((g.ball_card_bound o ell).trans
      (Nat.pow_le_pow_right (by omega : 0 < d + 1) hell))).trans hball
  have hcap : ∀ e, ‖f e‖ ≤ M :=
    g.outsideOrientedCavityValue_norm_bound T z C L hC hL hS hSi
  have hrenorm := g.outsideMean_normalization_difference T (by omega) (by omega) hT f M hM hcap
  have hηB : z.im ≤ B := ((le_abs_self _).trans (Complex.abs_im_le_norm _)).trans hzB
  have hward := deletion_density_ward_budget N (Nat.card T) B M z.im (by omega) hM hz hηB
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hsmall : ‖finiteComplexMean f - ((N : ℝ) * (d : ℝ))⁻¹ • ∑ e, f e‖ ≤
      graphPaperError a d N r z / Real.log (N : ℝ) ^ 16 := by
    apply deletion_change_absorption (Real.log (N : ℝ)) ((N : ℝ) * z.im)
      (graphPaperError a d N r z) (Nat.card T : ℝ) K ((d : ℝ) + 1) _ a b
      hlog ha hb (by positivity) (graphPaperError_nonnegative _ _ _ _ _ hN hz.le)
      (Nat.cast_nonneg _) hK (by positivity) hmargin
      (by have hh := (div_le_iff₀ hn).mp hscale; simpa only [mul_comm] using hh)
      (graphPaperError_fractional_lower _ _ _ _ _ hlog hz.le)
      (g.ball_card_log_bound o a ell hd hlog hell) (hrenorm.trans hward)
  have hfirst := hraw g o ell r z hell hz hzB hscale hR hRi hS hSi
  have htriangle := norm_sub_le_norm_sub_add_norm_sub (g.Q z)
    (((N : ℝ) * (d : ℝ))⁻¹ • ∑ e, f e) (finiteComplexMean f)
  have hsecond : ‖((N : ℝ) * (d : ℝ))⁻¹ • ∑ e, f e - finiteComplexMean f‖ ≤
      graphPaperError a d N r z / Real.log (N : ℝ) ^ 16 := by
    simpa only [norm_sub_rev] using hsmall
  exact htriangle.trans ((add_le_add hfirst hsecond).trans_eq (by ring))

end RegularGraph
end
end LocalLaw
