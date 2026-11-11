import LocalLaw.SourceSingletonObservation
import LocalLaw.EffectiveModelRadius

/-!
# Actual source parameters for the singleton observation

The shorter internal radius retains the nominal paper error. The actual
paper-error smallness, integer logarithmic radius and fixed large-log bounds
realize every finite observation condition, uniformly above the source
spectral floor, including beta=c/32.
-/

open Filter
noncomputable section
namespace LocalLaw

def sourceObservationLogCap (d : ℕ) (β : ℝ) : ℝ :=
  (6 * (finiteOmega d : ℝ) + 10) * (1 + β / Real.log ((d - 1 : ℕ) : ℝ))

theorem sourceObservationLogCap_nonnegative (d : ℕ) (hd : 3 ≤ d) (β : ℝ) (hβ : 0 ≤ β) :
    0 ≤ sourceObservationLogCap d β := by
  have hk : 1 < ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 < d - 1 by omega)
  unfold sourceObservationLogCap
  exact mul_nonneg (by positivity) (add_nonneg (by norm_num) (div_nonneg hβ (Real.log_pos hk).le))

private theorem singleton_observation_log_caps (n r : ℕ) (L θ : ℝ)
    (hL : 1 ≤ L) (hθ : 0 ≤ θ) (hr : (r : ℝ) ≤ θ * L) :
    (((((n + 1) * (4 * (r + 1) + 1) : ℕ) : ℝ) + 1 ≤ (6 * (n : ℝ) + 10) * (1 + θ) * L) ∧
      (((4 * r + 1 : ℕ) + 1 : ℝ) ≤ (6 * (n : ℝ) + 10) * (1 + θ) * L)) := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hL0 : 0 ≤ L := by linarith
  have hθL : 0 ≤ θ * L := mul_nonneg hθ hL0
  have hfirst := mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ 4 * (n : ℝ) + 4)
  have hsecond := mul_le_mul_of_nonneg_left hL (by positivity : 0 ≤ 5 * (n : ℝ) + 6)
  have hthird := mul_le_mul_of_nonneg_right
    (show 4 * (n : ℝ) + 4 ≤ 6 * (n : ℝ) + 10 by linarith) hθL
  have hfourth := mul_le_mul_of_nonneg_right
    (show 5 * (n : ℝ) + 6 ≤ 6 * (n : ℝ) + 10 by linarith) hL0
  have hdiam : (((n + 1) * (4 * (r + 1) + 1) : ℕ) : ℝ) + 1 ≤
      (6 * (n : ℝ) + 10) * (1 + θ) * L := by
    push_cast
    nlinarith only [hfirst, hsecond, hthird, hfourth]
  refine ⟨hdiam, ?_⟩
  have hnat : (4 * r + 1) + 1 ≤ (n + 1) * (4 * (r + 1) + 1) + 1 := by nlinarith
  have hreal : (((4 * r + 1 : ℕ) + 1 : ℝ)) ≤
      ((((n + 1) * (4 * (r + 1) + 1) : ℕ) : ℝ) + 1) := by exact_mod_cast hnat
  exact hreal.trans hdiam

/-- All source observation budgets follow from the actual nominal error,
effective radius and spectral floor, with no analytic bound assumed. -/
theorem eventually_sourceObservationBounds (a b d : ℕ) (c β B C1 : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hc : 0 < c)
    (hβ : 0 < β) (hβc : β ≤ c / 32) (hC1 : 1 ≤ C1) :
    ∀ᶠ N : ℕ in atTop, ∀ z : ℂ, 0 < z.im → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
      SourceObservationBounds d (effectiveModelRadius a d N β) z B C1
        (graphPaperError a d N (logarithmicRadius β d N) z) (Real.log (N : ℝ))
        (sourceObservationLogCap d β) := by
  let A := sourceObservationLogCap d β
  let K := DeficientGraph.localizationWeakConstant d B A
  let P := DeficientGraph.singletonPivotConstant d B
  let k : ℝ := ((d - 1 : ℕ) : ℝ)
  have hk : 1 < k := by dsimp only [k]; exact_mod_cast (show 1 < d - 1 by omega)
  have hlogk : 0 < Real.log k := Real.log_pos hk
  have hA : 0 ≤ A := sourceObservationLogCap_nonnegative d hd β hβ.le
  have hC0 : 0 ≤ C1 := (by norm_num : (0 : ℝ) ≤ 1).trans hC1
  have hC2 : 1 ≤ C1 ^ 2 := by nlinarith
  filter_upwards [eventually_paperError_small a b d β ha hb hd hβ,
    eventually_effectiveModelRadius_margins a d c β (by omega) hd hc hβ hβc,
    eventually_log_ge_nat 1, eventually_log_ge_nat (C1 ^ 2), eventually_log_ge_nat (K * C1),
    eventually_log_ge_nat (4 * P), eventually_log_ge_nat (DeficientGraph.localizationBudgetConstant d B A),
    eventually_log_ge_nat (k ^ 4), eventually_ge_atTop 1]
    with N hsmall hradii hlog hCLog hfeedback hpivot hlarge hkLog hN
  intro z hz hfloor
  let L := Real.log (N : ℝ)
  let r := effectiveModelRadius a d N β
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  have hLpos : 0 < L := by linarith
  have hε : 0 ≤ ε := graphPaperError_nonnegative a d N _ z hN hz.le
  have hfullCap : ε * L ^ (4 * a) ≤ 1 := by
    exact (le_div_iff₀ (pow_pos hLpos _)).mp (by simpa only [one_div] using hsmall z hz hfloor)
  have hε5 : ε * L ^ 5 ≤ 1 :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hlog (show 5 ≤ 4 * a by omega)) hε).trans hfullCap
  have hscaled : (C1 ^ 2 * ε) * L ^ 4 ≤ 1 := by
    calc
      _ = C1 ^ 2 * (ε * L ^ 4) := by ring
      _ ≤ L * (ε * L ^ 4) := mul_le_mul_of_nonneg_right hCLog (by positivity)
      _ = ε * L ^ 5 := by ring
      _ ≤ _ := hε5
  have hrnom : (logarithmicRadius β d N : ℝ) ≤ (β / Real.log k) * L := by
    have hh := Nat.floor_le (div_nonneg (mul_nonneg hβ.le hLpos.le) hlogk.le)
    change (logarithmicRadius β d N : ℝ) ≤ β * L / Real.log k at hh
    exact hh.trans_eq (by ring)
  have hre : (r : ℝ) ≤ (β / Real.log k) * L :=
    (Nat.cast_le.mpr hradii.2.2.1).trans hrnom
  have hcaps := singleton_observation_log_caps (finiteOmega d) r L (β / Real.log k) hlog
    (div_nonneg hβ.le hlogk.le) hre
  have htail := effectiveModelRadius_localization_tail a d N β hd hlog hradii.1 z hz.le
  have hpower : k ^ 4 ≤ L ^ (4 * a) := hkLog.trans
    (by simpa only [pow_one] using pow_le_pow_right₀ hlog (show 1 ≤ 4 * a by omega))
  have htailε : physicalTransfer d z ^ (2 * r) ≤ ε := by
    apply htail.trans
    apply (div_le_iff₀ (pow_pos hLpos _)).mpr
    have hh := mul_le_mul_of_nonneg_right hpower hε
    nlinarith only [hh]
  refine ⟨hε, hlog, hA, hC1, hscaled, hcaps.1, hcaps.2, hlarge, ?_, hpivot, ?_⟩
  · exact hfeedback.trans (by nlinarith only [hlog])
  · exact htailε.trans (le_mul_of_one_le_left hε hC2)

namespace RegularGraph

/-- Actual source (6.4), uniformly over all sampling edges, follows on the
independent-radius OmegaPlus event at the endpoint-compatible model radius.
No finite observation, localization or pivot premise remains. -/
theorem eventually_sourceSingletonObservation_bound (a b d : ℕ) (c β B C1 : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hc : 0 < c)
    (hβ : 0 < β) (hβc : β ≤ c / 32) (hC1 : 1 ≤ C1) :
    ∀ᶠ N : ℕ in atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0 < z.im → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im → ‖z‖ ≤ B →
      ∀ Cq badCount : ℕ,
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c / 4) d N) (actualCavityDepth a d N z - 1) (finiteOmega d)
        Cq badCount C1 o z →
      ∀ e : OutsideOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1)),
      ‖g.sourceSingletonObservation (graphBallVertices g.graph o (actualCavityDepth a d N z - 1))
        (effectiveModelRadius a d N β) (logarithmicRadius (c / 4) d N / 4) z (g.Q z) e‖ ≤
        DeficientGraph.singletonObservationConstant d * C1 *
          g.sourcePrime a (logarithmicRadius β d N) z := by
  filter_upwards [eventually_sourceObservationBounds a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_effectiveModelRadius_margins a d c β (by omega) hd hc hβ hβc]
    with N hbounds hradii
  intro g o z hz hfloor hB Cq badCount hplus e
  have hmargin := hradii.2.2.2 z
  have hm : effectiveModelRadius a d N β + 1 ≤ logarithmicRadius (c / 4) d N / 8 := by omega
  have hfar : effectiveModelRadius a d N β + 2 ≤ logarithmicRadius (c / 4) d N / 4 := by omega
  exact g.sourceSingletonObservation_bound a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
    (logarithmicRadius (c / 4) d N) (actualCavityDepth a d N z - 1) Cq badCount C1 B
    (sourceObservationLogCap d β) o z hplus hd hz hB (hbounds z hz hfloor) hm hfar e

end RegularGraph
end LocalLaw
