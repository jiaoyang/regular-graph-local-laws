import LocalLaw.ExteriorCavityAnchor
import LocalLaw.ScalarStability
import LocalLaw.SpectralScaleContinuity

/-!
# Exterior local-law rates on the unbounded spectral domain

The finite moment comparison retains its spectral factor 1/‖z‖. Actual entry
and trace bounds therefore fit the same square-root error scale throughout the
unbounded exterior domain. The exceptional-center density remains explicit.
-/

open scoped BigOperators

namespace LocalLaw

/-- Half of the spectral modulus remains in the exterior row gap. -/
theorem normalized_exterior_half_gap (d : ℕ) (hd : 3 ≤ d) (z : ℂ)
    (hz : 2 * (d : ℝ) ≤ ‖z‖) :
    ‖z‖ / 2 ≤ ‖z‖ - (d : ℝ) / Real.sqrt ((d : ℝ) - 1) := by
  have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
  have hs : 0 < Real.sqrt ((d : ℝ) - 1) := Real.sqrt_pos.mpr (by linarith)
  have hsone : 1 ≤ Real.sqrt ((d : ℝ) - 1) := by
    have hh := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ d - 1 by linarith)
    simpa only [Real.sqrt_one] using hh
  have hM : (d : ℝ) / Real.sqrt ((d : ℝ) - 1) ≤ d := by
    apply (div_le_iff₀ hs).mpr
    nlinarith [mul_le_mul_of_nonneg_left hsone (by linarith : (0 : ℝ) ≤ d)]
  linarith

/-- The extra odd moment factor supplies a half, giving the unbounded-domain
rate 2(d-1)^(-r)/‖z‖. -/
theorem normalized_exterior_localization_spectral_rate (d : ℕ) (hd : 3 ≤ d) (z : ℂ)
    (hz : 2 * (d : ℝ) ≤ ‖z‖) (r : ℕ) :
    let M := (d : ℝ) / Real.sqrt ((d : ℝ) - 1)
    2 * (M / ‖z‖) ^ (2 * r + 1) / (‖z‖ - M) ≤
      2 * (1 / (((d : ℝ) - 1) ^ r)) / ‖z‖ := by
  obtain ⟨hM, hgap, _, hratio⟩ := normalized_exterior_constants d hd z hz
  have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
  have hkpos : 0 < (d : ℝ) - 1 := by linarith
  have hspos : 0 < Real.sqrt ((d : ℝ) - 1) := Real.sqrt_pos.mpr hkpos
  have hsone : 1 ≤ Real.sqrt ((d : ℝ) - 1) := by
    have hh := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ d - 1 by linarith)
    simpa only [Real.sqrt_one] using hh
  have hzpos : 0 < ‖z‖ := by linarith [norm_nonneg z]
  let ρ := ((d : ℝ) / Real.sqrt ((d : ℝ) - 1)) / ‖z‖
  have hρ0 : 0 ≤ ρ := div_nonneg hM (norm_nonneg _)
  have hρhalf : ρ ≤ 1 / 2 := hratio.trans
    (one_div_le_one_div_of_le (by norm_num) (by linarith))
  have hρsqrt : ρ ≤ (Real.sqrt ((d : ℝ) - 1))⁻¹ := hratio.trans (by
    rw [← one_div]
    exact one_div_le_one_div_of_le hspos (by linarith))
  have hbase : ρ ^ 2 ≤ 1 / ((d : ℝ) - 1) := by
    have hp := pow_le_pow_left₀ hρ0 hρsqrt 2
    rwa [inv_pow, Real.sq_sqrt hkpos.le, ← one_div] at hp
  have hpow : ρ ^ (2 * r + 1) ≤ (1 / (((d : ℝ) - 1) ^ r)) / 2 := by
    calc
      ρ ^ (2 * r + 1) = (ρ ^ 2) ^ r * ρ := by rw [pow_add, pow_one, pow_mul]
      _ ≤ (1 / ((d : ℝ) - 1)) ^ r * (1 / 2) :=
        mul_le_mul (pow_le_pow_left₀ (sq_nonneg _) hbase r) hρhalf hρ0 (by positivity)
      _ = (1 / (((d : ℝ) - 1) ^ r)) / 2 := by rw [one_div_pow]; ring
  have hgapPos : 0 < ‖z‖ - (d : ℝ) / Real.sqrt ((d : ℝ) - 1) := sub_pos.mpr hgap
  change 2 * ρ ^ (2 * r + 1) / (‖z‖ - _) ≤ _
  calc
    _ ≤ 2 * ((1 / (((d : ℝ) - 1) ^ r)) / 2) / (‖z‖ / 2) :=
      div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hpow (by norm_num))
        (by positivity) (normalized_exterior_half_gap d hd z hz)
    _ = 2 * (1 / (((d : ℝ) - 1) ^ r)) / ‖z‖ := by ring

/-- The actual regular-tree reference also decays on the unbounded exterior.
A direct scalar denominator estimate gives the stronger constant two. -/
theorem kestenMcKay_exterior_spectral_norm (d : ℕ) (hd : 3 ≤ d) (z m : ℂ)
    (hm : ‖m‖ ≤ 1) (hz : 2 * (d : ℝ) ≤ ‖z‖) :
    ‖kestenMcKayTransform d m z‖ ≤ 2 / ‖z‖ := by
  have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
  have hkpos : 0 < ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < d - 1 by omega)
  have hkcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hq : ‖(d : ℂ) / ((d - 1 : ℕ) : ℂ)‖ ≤ 2 := by
    simp only [norm_div, Complex.norm_natCast]
    apply (div_le_iff₀ hkpos).mpr
    rw [hkcast]
    linarith
  have hself : ‖((d : ℂ) / ((d - 1 : ℕ) : ℂ)) * m‖ ≤ 2 := by
    rw [norm_mul]
    exact (mul_le_mul hq hm (norm_nonneg _) (by norm_num)).trans_eq (mul_one _)
  have hden : ‖z‖ / 2 ≤ ‖-z - ((d : ℂ) / ((d - 1 : ℕ) : ℂ)) * m‖ := by
    have hh := norm_sub_norm_le (-z) (((d : ℂ) / ((d - 1 : ℕ) : ℂ)) * m)
    rw [norm_neg] at hh
    linarith
  have hzpos : 0 < ‖z‖ := by linarith [norm_nonneg z]
  rw [kestenMcKayTransform, norm_inv, ← one_div]
  calc
    _ ≤ 1 / (‖z‖ / 2) := one_div_le_one_div_of_le (by positivity) hden
    _ = 2 / ‖z‖ := by ring

/-- Beyond modulus three the regularized edge square root is no larger than
the modulus, uniformly for every error at most one. -/
theorem exterior_sqrt_scale_le_norm (z : ℂ) (hz : 3 ≤ ‖z‖) (ε : ℝ) (hε : ε ≤ 1) :
    Real.sqrt (spectralScale z + ε) ≤ ‖z‖ := by
  have hzero : spectralScale (0 : ℂ) = 2 := by norm_num [spectralScale, edgeDistance]
  have hs := spectralScale_lipschitz z 0
  rw [hzero, dist_zero_right] at hs
  have hcap : spectralScale z ≤ 2 * ‖z‖ + 2 := by
    linarith [(le_abs_self (spectralScale z - 2)).trans hs]
  apply Real.sqrt_le_iff.mpr
  refine ⟨norm_nonneg _, ?_⟩
  nlinarith [mul_nonneg (sub_nonneg.mpr hz) (by linarith : (0 : ℝ) ≤ ‖z‖ + 1)]

/-- Conversion of the exterior spectral rate to the common local-law scale.
The only lower error requirement is ε≥2δ. -/
theorem exterior_spectral_rate_le_scalarScale (z : ℂ) (hzIm : 0 < z.im)
    (hz : 3 ≤ ‖z‖) (δ ε : ℝ) (hδ : 0 ≤ δ) (hbudget : 2 * δ ≤ ε) (hε : ε ≤ 1) :
    2 * δ / ‖z‖ ≤ scalarScale (spectralScale z) ε := by
  have hε0 : 0 ≤ ε := (mul_nonneg (by norm_num) hδ).trans hbudget
  have hroot : 0 < Real.sqrt (spectralScale z + ε) :=
    Real.sqrt_pos.mpr (add_pos_of_pos_of_nonneg (spectralScale_pos hzIm) hε0)
  calc
    _ ≤ 2 * δ / Real.sqrt (spectralScale z + ε) :=
      div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hδ) hroot
        (exterior_sqrt_scale_le_norm z hz ε hε)
    _ ≤ scalarScale (spectralScale z) ε :=
      div_le_div_of_nonneg_right hbudget hroot.le

noncomputable section
local instance exteriorRateDecidable (p : Prop) : Decidable p := Classical.propDecidable p

namespace RegularGraph
variable {N d : ℕ}

/-- Actual pair-neighborhood comparison retaining the spectral decay. -/
theorem exterior_pair_approximation_spectral (g : RegularGraph N d) (hd : 3 ≤ d)
    (r : ℕ) (z w : ℂ) (hw : ‖w‖ ≤ 1) (hz : 2 * (d : ℝ) ≤ ‖z‖) (i j : Fin N) :
    ‖g.G z i j - g.P r z w i j‖ ≤ 2 * (1 / (((d : ℝ) - 1) ^ r)) / ‖z‖ := by
  obtain ⟨hM, hgap, _, _⟩ := normalized_exterior_constants d hd z hz
  have hHrow : ∀ v, ∑ u, ‖g.H v u‖ ≤ (d : ℝ) / Real.sqrt ((d : ℝ) - 1) := by
    intro v
    rw [H, normalizedAdjacency_row_sum, g.regular v]
  have hmoments : ∀ n < 2 * r + 1, (g.H ^ n) i j =
      (g.pairExtensionMatrix r w i j ^ n) (pairBallLeft g.graph i j r) (pairBallRight g.graph i j r) := by
    intro n hn
    exact g.pairExtension_power_eq r w i j n (by omega)
  have hh := resolvent_moment_matching_bound g.H (g.pairExtensionMatrix r w i j)
    z _ hM hHrow (g.pairExtension_row_sum_bound hd r w hw i j) hgap (2 * r + 1) i j
    (pairBallLeft g.graph i j r) (pairBallRight g.graph i j r) hmoments
  rw [g.P_eq_green_pairExtension]
  exact hh.trans (normalized_exterior_localization_spectral_rate d hd z hz r)

/-- Genuine actual graph inverse entries decay as 2/‖z‖ in the exterior. -/
theorem G_exterior_spectral_norm (g : RegularGraph N d) (hd : 3 ≤ d)
    (z : ℂ) (hz : 2 * (d : ℝ) ≤ ‖z‖) (i j : Fin N) : ‖g.G z i j‖ ≤ 2 / ‖z‖ := by
  obtain ⟨_, hgap, _, _⟩ := normalized_exterior_constants d hd z hz
  have hrow : ∀ v, ∑ u, ‖g.H v u‖ ≤ (d : ℝ) / Real.sqrt ((d : ℝ) - 1) := by
    intro v
    rw [H, normalizedAdjacency_row_sum, g.regular v]
  have hh := exterior_green_entry_bound g.H z _ hrow hgap
    (spectralMatrix_isUnit_of_row_gap g.H z _ hrow hgap) i j
  have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
  have hzpos : 0 < ‖z‖ := by linarith [norm_nonneg z]
  exact hh.trans ((one_div_le_one_div_of_le (by positivity)
    (normalized_exterior_half_gap d hd z hz)).trans_eq (by ring))

/-- The same actual inverse bound holds for every norm-one boundary parameter. -/
theorem P_exterior_spectral_norm (g : RegularGraph N d) (hd : 3 ≤ d)
    (r : ℕ) (z w : ℂ) (hw : ‖w‖ ≤ 1) (hz : 2 * (d : ℝ) ≤ ‖z‖)
    (i j : Fin N) : ‖g.P r z w i j‖ ≤ 2 / ‖z‖ := by
  obtain ⟨_, hgap, _, _⟩ := normalized_exterior_constants d hd z hz
  rw [g.P_eq_green_pairExtension]
  have hh := exterior_green_entry_bound (g.pairExtensionMatrix r w i j) z _
    (g.pairExtension_row_sum_bound hd r w hw i j) hgap
    (spectralMatrix_isUnit_of_row_gap _ z _ (g.pairExtension_row_sum_bound hd r w hw i j) hgap)
    (pairBallLeft g.graph i j r) (pairBallRight g.graph i j r)
  have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
  have hzpos : 0 < ‖z‖ := by linarith [norm_nonneg z]
  exact hh.trans ((one_div_le_one_div_of_le (by positivity)
    (normalized_exterior_half_gap d hd z hz)).trans_eq (by ring))

/-- The exterior normalized trace estimate retains the sparse geometric error
with its spectral decay. No probabilistic exceptional-count bound is assumed. -/
theorem empirical_exterior_spectral_error (g : RegularGraph N d) (hN : 0 < N)
    (hd : 3 ≤ d) (r R : ℕ) (hR : r ≤ R) (z : ℂ) (hzIm : 0 < z.im)
    (hz : 2 * (d : ℝ) ≤ ‖z‖) :
    ‖empiricalTransform g.H z - graphKestenMcKayReference d z‖ ≤
      2 * (1 / (((d : ℝ) - 1) ^ r)) / ‖z‖ +
        ((nonTreeCenters g.graph R).card : ℝ) / (N : ℝ) * (6 / ‖z‖) := by
  let p := graphKestenMcKayReference d z
  let a := 2 * (1 / (((d : ℝ) - 1) ^ r)) / ‖z‖
  let f := fun i => g.G z i i - p
  have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
  have hzpos : 0 < ‖z‖ := by linarith [norm_nonneg z]
  have hkpos : 0 < (d : ℝ) - 1 := by linarith
  have hapos : 0 ≤ a := by dsimp [a]; positivity
  have hp : ‖p‖ ≤ 2 / ‖z‖ := kestenMcKay_exterior_spectral_norm d hd z
    (semicircleRoot z) (semicircleRoot_norm_le_one z) hz
  have hgood : ∀ i, i ∉ nonTreeCenters g.graph R → ‖f i‖ ≤ a := by
    intro i hi
    have htree : (graphBall g.graph i R).IsTree :=
      not_not.mp (fun hn => hi ((nonTreeCenters_membership g.graph R i).mpr hn))
    have hforest : (pairBallGraph g.graph i i r).IsAcyclic := by
      apply induced_acyclic_mono g.graph _ htree.2
      intro v hv
      exact (hv.elim id id).trans (ENat.coe_le_coe.mpr hR)
    have hlocal := g.exterior_pair_approximation_spectral hd r z (semicircleRoot z)
      (semicircleRoot_norm_le_one z) hz i i
    rw [g.P_reference_diagonal_of_acyclic hd r z hzIm i hforest] at hlocal
    exact hlocal
  have hbad : ∀ i, i ∈ nonTreeCenters g.graph R → ‖f i‖ ≤ a + 6 / ‖z‖ := by
    intro i _
    have hh := (norm_sub_le (g.G z i i) p).trans
      (add_le_add (g.G_exterior_spectral_norm hd z hz i i) hp)
    dsimp [f]
    have heq : 6 / ‖z‖ = 2 / ‖z‖ + 2 / ‖z‖ + 2 / ‖z‖ := by ring
    rw [heq]
    linarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hzpos.le]
  have hh := sparse_average_bound f (nonTreeCenters g.graph R) a (6 / ‖z‖)
    (by simpa only [Fintype.card_fin] using hN) hgood hbad
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hN)
  have hid : empiricalTransform g.H z - p = (N : ℂ)⁻¹ * ∑ i, f i := by
    simp only [empiricalTransform, Matrix.trace, Fintype.card_fin, f,
      Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    change (N : ℂ)⁻¹ * ∑ i, g.G z i i - p = _
    field_simp
  rw [hid]
  simpa only [Fintype.card_fin, Complex.real_smul, Complex.ofReal_inv,
    Complex.ofReal_natCast] using hh

/-- Entry local law on the entire exterior, with the actual random boundary Q.
No geometric exceptional-count hypothesis is required for this entry estimate. -/
theorem exterior_entry_local_law (g : RegularGraph N d) (hN : 0 < N) (hd : 3 ≤ d)
    (r : ℕ) (z : ℂ) (hzIm : 0 < z.im) (hz : 2 * (d : ℝ) ≤ ‖z‖) (ε : ℝ)
    (hbudget : 2 * (1 / (((d : ℝ) - 1) ^ r)) ≤ ε) (hε : ε ≤ 1) (i j : Fin N) :
    ‖g.G z i j - g.P r z (g.Q z) i j‖ ≤ scalarScale (spectralScale z) ε := by
  have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
  have hkpos : 0 < (d : ℝ) - 1 := by linarith
  have hQ : ‖g.Q z‖ ≤ 1 := (g.Q_exterior_norm hN hd z hz).trans
    ((div_le_one (by linarith : (0 : ℝ) < d)).mpr (by linarith))
  exact (g.exterior_pair_approximation_spectral hd r z (g.Q z) hQ hz i j).trans
    (exterior_spectral_rate_le_scalarScale z hzIm (by linarith) _ ε (by positivity) hbudget hε)

/-- Trace local law on the entire exterior. A bound Mδ on the actual density
of bad radius-R centers appears only in the explicit constant 1+3M. -/
theorem exterior_trace_local_law (g : RegularGraph N d) (hN : 0 < N) (hd : 3 ≤ d)
    (r R : ℕ) (hR : r ≤ R) (z : ℂ) (hzIm : 0 < z.im) (hz : 2 * (d : ℝ) ≤ ‖z‖)
    (ε M : ℝ) (hM : 0 ≤ M)
    (hbad : ((nonTreeCenters g.graph R).card : ℝ) / (N : ℝ) ≤
      M * (1 / (((d : ℝ) - 1) ^ r)))
    (hbudget : 2 * (1 / (((d : ℝ) - 1) ^ r)) ≤ ε) (hε : ε ≤ 1) :
    ‖empiricalTransform g.H z - graphKestenMcKayReference d z‖ ≤
      (1 + 3 * M) * scalarScale (spectralScale z) ε := by
  have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
  have hzpos : 0 < ‖z‖ := by linarith [norm_nonneg z]
  have hkpos : 0 < (d : ℝ) - 1 := by linarith
  calc
    _ ≤ 2 * (1 / (((d : ℝ) - 1) ^ r)) / ‖z‖ +
        (((nonTreeCenters g.graph R).card : ℝ) / (N : ℝ)) * (6 / ‖z‖) :=
      g.empirical_exterior_spectral_error hN hd r R hR z hzIm hz
    _ ≤ 2 * (1 / (((d : ℝ) - 1) ^ r)) / ‖z‖ +
        (M * (1 / (((d : ℝ) - 1) ^ r))) * (6 / ‖z‖) :=
      add_le_add_left (mul_le_mul_of_nonneg_right hbad (by positivity)) _
    _ = (1 + 3 * M) * (2 * (1 / (((d : ℝ) - 1) ^ r)) / ‖z‖) := by ring
    _ ≤ (1 + 3 * M) * scalarScale (spectralScale z) ε :=
      mul_le_mul_of_nonneg_left
        (exterior_spectral_rate_le_scalarScale z hzIm (by linarith) _ ε (by positivity) hbudget hε)
        (by positivity)

/-- Entry and trace conclusions on the full exterior with a single numeric
error budget and an explicit sparse-geometric density assumption. -/
theorem exterior_entry_trace_local_law (g : RegularGraph N d) (hN : 0 < N) (hd : 3 ≤ d)
    (r R : ℕ) (hR : r ≤ R) (z : ℂ) (hzIm : 0 < z.im) (hz : 2 * (d : ℝ) ≤ ‖z‖)
    (ε M : ℝ) (hM : 0 ≤ M)
    (hbad : ((nonTreeCenters g.graph R).card : ℝ) / (N : ℝ) ≤
      M * (1 / (((d : ℝ) - 1) ^ r)))
    (hbudget : 2 * (1 / (((d : ℝ) - 1) ^ r)) ≤ ε) (hε : ε ≤ 1) :
    (∀ i j, ‖g.G z i j - g.P r z (g.Q z) i j‖ ≤ scalarScale (spectralScale z) ε) ∧
      ‖empiricalTransform g.H z - graphKestenMcKayReference d z‖ ≤
        (1 + 3 * M) * scalarScale (spectralScale z) ε :=
  ⟨g.exterior_entry_local_law hN hd r z hzIm hz ε hbudget hε,
    g.exterior_trace_local_law hN hd r R hR z hzIm hz ε M hM hbad hbudget hε⟩

end RegularGraph
end

end LocalLaw
