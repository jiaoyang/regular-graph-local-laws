import LocalLaw.SwitchingPerturbationMass
import LocalLaw.SharpSamplingCounts
import LocalLaw.ParameterCorrelation

/-!
# Actual absorption of the resampling Q-change budget

On a bounded spectral disk, a uniform actual Green/pivot cap gives a change
O(mu/(N eta)). The fractional source-error component and actual sampling scale
absorb this into epsilon/(log N)^16. No Q-change estimate is an input to the
final resampling corollary: it comes from the checked switching/Ward identity.
-/

open scoped BigOperators
namespace LocalLaw
noncomputable section
local instance switchingQParameterDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def switchingQConstant (C L B : ℝ) : ℝ :=
  8 * ((1 + C * L) ^ 2 * C + B * (C + C ^ 2 * L))

theorem switchingQConstant_nonnegative (C L B : ℝ)
    (hC : 0 ≤ C) (hL : 0 ≤ L) (hB : 0 ≤ B) : 0 ≤ switchingQConstant C L B := by
  unfold switchingQConstant
  positivity

/-- The actual finite switching bound has the simpler mu/(N eta) scale. -/
theorem switching_Q_budget_le (N d : ℕ) (μ C L B η : ℝ)
    (hN : 0 < N) (hd : 3 ≤ d) (hμ : 0 ≤ μ) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hη : 0 < η) (hηB : η ≤ B) :
    ((N : ℝ) * (d : ℝ))⁻¹ *
      (((d : ℝ) * (1 + C * L) ^ 2 * C / η) * (8 * μ / Real.sqrt ((d : ℝ) - 1)) +
        8 * μ * (C + C ^ 2 * L)) ≤ switchingQConstant C L B * μ / ((N : ℝ) * η) := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
  have hdp : (0 : ℝ) < d := by linarith
  have hsqrt : 1 ≤ Real.sqrt ((d : ℝ) - 1) := Real.one_le_sqrt.mpr (by linarith)
  have hμdiv : 8 * μ / Real.sqrt ((d : ℝ) - 1) ≤ 8 * μ := div_le_self (by positivity) hsqrt
  have hsmall : (C + C ^ 2 * L) / (d : ℝ) ≤ B * (C + C ^ 2 * L) / η := by
    apply (div_le_self (by positivity : 0 ≤ C + C ^ 2 * L) (by linarith : (1 : ℝ) ≤ d)).trans
    apply (le_div_iff₀ hη).mpr
    nlinarith [mul_le_mul_of_nonneg_right hηB (show 0 ≤ C + C ^ 2 * L by positivity)]
  calc
    _ ≤ ((N : ℝ) * (d : ℝ))⁻¹ *
        (((d : ℝ) * (1 + C * L) ^ 2 * C / η) * (8 * μ) + 8 * μ * (C + C ^ 2 * L)) := by
      gcongr
    _ = 8 * μ / (N : ℝ) * ((1 + C * L) ^ 2 * C / η + (C + C ^ 2 * L) / (d : ℝ)) := by
      field_simp
      ring
    _ ≤ 8 * μ / (N : ℝ) * ((1 + C * L) ^ 2 * C / η + B * (C + C ^ 2 * L) / η) :=
      mul_le_mul_of_nonneg_left (add_le_add_left hsmall _) (by positivity)
    _ = _ := by unfold switchingQConstant; field_simp; ring

/-- The fractional source-error term is a lower bound on the inflated error,
including either inflation branch. -/
theorem graphPaperError_fractional_lower (a d N r : ℕ) (z : ℂ)
    (hlog : 1 ≤ Real.log (N : ℝ)) (hz : 0 ≤ z.im) :
    Real.log (N : ℝ) ^ (8 * a) / (((N : ℝ) * z.im) ^ (2 / 3 : ℝ)) ≤
      graphPaperError a d N r z := by
  have hbase := (baseError_component_bounds (Real.log (N : ℝ)) a d N r z.im
    (graphKestenMcKayReference d z).im (by linarith) hz).2.2
  have he0 := baseError_nonnegative (Real.log (N : ℝ)) a d N r z.im
    (graphKestenMcKayReference d z).im (by linarith) hz
  calc
    _ = Real.log (N : ℝ) ^ (8 * a) * (((N : ℝ) * z.im) ^ (2 / 3 : ℝ))⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ baseError (Real.log (N : ℝ)) a d N r z.im (graphKestenMcKayReference d z).im := hbase
    _ ≤ _ := (inflateError_bounds (s := spectralScale z) hlog he0).1

/-- An explicit finite logarithmic absorption of the Ward change scale. -/
theorem switching_change_absorption (ℓ X ε μ K M δ : ℝ) (a b : ℕ)
    (hℓ : 1 ≤ ℓ) (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hX : 0 < X)
    (hε : 0 ≤ ε) (hK : 0 ≤ K) (_hM : 0 ≤ M) (hmargin : K * M ≤ ℓ)
    (hsample : ℓ ^ b ≤ X) (hfraction : ℓ ^ (8 * a) / X ^ (2 / 3 : ℝ) ≤ ε)
    (hμ : μ ≤ M * ℓ ^ (2 * a)) (hδ : δ ≤ K * μ / X) : δ ≤ ε / ℓ ^ 16 := by
  have hℓp : 0 < ℓ := by linarith
  have hlower := fractional_component_sample_lower ℓ X ε a b hℓ hX hε hfraction hsample (by omega)
  have hpow : ℓ ^ (2 * a + 17) ≤ ℓ ^ (12 * a + 4) := pow_le_pow_right₀ hℓ (by omega)
  have hscaled : K * μ * ℓ ^ 16 ≤ ε * X := by
    calc
      _ ≤ (K * (M * ℓ ^ (2 * a))) * ℓ ^ 16 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hμ hK) (pow_nonneg hℓp.le _)
      _ = (K * M) * ℓ ^ (2 * a + 16) := by rw [pow_add]; ring
      _ ≤ ℓ * ℓ ^ (2 * a + 16) := mul_le_mul_of_nonneg_right hmargin (pow_nonneg hℓp.le _)
      _ = ℓ ^ (2 * a + 17) := by rw [show 2 * a + 17 = (2 * a + 16) + 1 by omega, pow_succ]; exact mul_comm _ _
      _ ≤ ε * X := hpow.trans hlower
  apply hδ.trans
  apply (div_le_iff₀ hX).mpr
  apply (mul_le_mul_right (pow_pos hℓp 16)).mp
  calc
    _ ≤ ε * X := hscaled
    _ = (ε / ℓ ^ 16 * X) * ℓ ^ 16 := by field_simp

/-- Uniform actual source-parameter realization of the absorption. -/
theorem eventually_switching_change_absorption (a b d : ℕ) (K M : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hK : 0 ≤ K) (hM : 0 ≤ M) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (z : ℂ) (r : ℕ) (μ δ : ℝ), 0 < z.im →
      Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
      μ ≤ M * Real.log (N : ℝ) ^ (2 * a) → δ ≤ K * μ / ((N : ℝ) * z.im) →
      δ ≤ graphPaperError a d N r z / Real.log (N : ℝ) ^ 16 := by
  filter_upwards [eventually_log_ge_nat 1, eventually_log_ge_nat (K * M),
    Filter.eventually_ge_atTop 1] with N hlog hmargin hN
  intro z r μ δ hz hscale hμ hδ
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hs : Real.log (N : ℝ) ^ b ≤ (N : ℝ) * z.im := by
    have hh := (div_le_iff₀ hn).mp hscale
    simpa only [mul_comm] using hh
  exact switching_change_absorption (Real.log (N : ℝ)) ((N : ℝ) * z.im)
    (graphPaperError a d N r z) μ K M δ a b hlog ha hb (by positivity)
    (graphPaperError_nonnegative _ _ _ _ _ hN hz.le) hK hM hmargin hs
    (graphPaperError_fractional_lower _ _ _ _ _ hlog hz.le) hμ hδ

namespace LabelledResamplingState

/-- The full physical resampling Q-change is eventually smaller than the
source error by sixteen logarithmic powers. Actual Green/pivot caps are the
remaining analytic inputs; no change-of-Q bound is a hypothesis. -/
theorem eventually_fullResample_cavity_change_small (a b d : ℕ) (C L B M : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d)
    (hC : 0 ≤ C) (hL : 0 ≤ L) (hB : 0 ≤ B) (hM : 0 ≤ M) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (T : Set (Fin N)) (ι : Type) [Fintype ι]
      (s : LabelledResamplingState (Fin N) T ι) (radius r : ℕ) (z : ℂ),
      s.graph.IsRegularOfDegree d → 0 < z.im → ‖z‖ ≤ B →
      Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
      (Nat.card (BoundaryOrientedEdge s.graph T) : ℝ) ≤ M * Real.log (N : ℝ) ^ (2 * a) →
      (∀ i j, ‖green (normalizedAdjacency s.graph d) z i j‖ ≤ C) →
      (∀ i j, ‖green (normalizedAdjacency (s.fullResample radius).graph d) z i j‖ ≤ C) →
      (∀ j, ‖(green (normalizedAdjacency s.graph d) z j j)⁻¹‖ ≤ L) →
      (∀ j, ‖(green (normalizedAdjacency (s.fullResample radius).graph d) z j j)⁻¹‖ ≤ L) →
      ‖cavityAverage s.graph d z - cavityAverage (s.fullResample radius).graph d z‖ ≤
        graphPaperError a d N r z / Real.log (N : ℝ) ^ 16 := by
  have hK := switchingQConstant_nonnegative C L B hC hL hB
  filter_upwards [eventually_switching_change_absorption a b d (switchingQConstant C L B) M
    ha hb hK hM, Filter.eventually_ge_atTop 1] with N habs hN
  intro T ι _ s radius r z hregular hz hzB hscale hμ hG hF hGi hFi
  apply habs z r (Nat.card (BoundaryOrientedEdge s.graph T) : ℝ) _ hz hscale hμ
  have hraw := s.fullResample_cavityAverage_difference_uniform radius d hregular z hz C L hC hL hG hF hGi hFi
  have hraw' := switching_Q_budget_le N d (Nat.card (BoundaryOrientedEdge s.graph T) : ℝ)
    C L B z.im (by omega) hd (Nat.cast_nonneg _) hC hL hz
    (((le_abs_self z.im).trans (Complex.abs_im_le_norm z)).trans hzB)
  simp only [Fintype.card_fin] at hraw
  exact hraw.trans hraw'

/-- The actual selected-radius boundary count is supplied by sharp graph
counting, so it is no longer an input in this source resampling corollary. -/
theorem eventually_selected_fullResample_cavity_change_small (a b d : ℕ) (C L B : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d)
    (hC : 0 ≤ C) (hL : 0 ≤ L) (hB : 0 ≤ B) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0 < z.im → ‖z‖ ≤ B → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
      ∀ (ι : Type) [Fintype ι]
        (s : LabelledResamplingState (Fin N)
          (graphBallVertices g.graph o (actualCavityDepth a d N z - 1)) ι)
        (radius r : ℕ), s.graph = g.graph →
      (∀ i j, ‖green (normalizedAdjacency s.graph d) z i j‖ ≤ C) →
      (∀ i j, ‖green (normalizedAdjacency (s.fullResample radius).graph d) z i j‖ ≤ C) →
      (∀ j, ‖(green (normalizedAdjacency s.graph d) z j j)⁻¹‖ ≤ L) →
      (∀ j, ‖(green (normalizedAdjacency (s.fullResample radius).graph d) z j j)⁻¹‖ ≤ L) →
      ‖g.Q z - cavityAverage (s.fullResample radius).graph d z‖ ≤
        graphPaperError a d N r z / Real.log (N : ℝ) ^ 16 := by
  filter_upwards [eventually_fullResample_cavity_change_small a b d C L B
    ((d : ℝ) * ((d : ℝ) + 1)) ha hb hd hC hL hB (by positivity),
    eventually_actual_boundary_card_log_bound a d hd (by omega)] with N habs hμ
  intro g o z hz hzB hscale ι _ s radius r hs hG hF hGi hFi
  have hreg : s.graph.IsRegularOfDegree d := by rw [hs]; exact g.regular
  have hcount : (Nat.card (BoundaryOrientedEdge s.graph
      (graphBallVertices g.graph o (actualCavityDepth a d N z - 1))) : ℝ) ≤
      (d : ℝ) * ((d : ℝ) + 1) * Real.log (N : ℝ) ^ (2 * a) := by
    simpa only [hs] using hμ g o z
  have hh := habs _ ι s radius r z hreg hz hzB hscale hcount hG hF hGi hFi
  simpa only [hs, RegularGraph.Q] using hh

end LabelledResamplingState

end
end LocalLaw
