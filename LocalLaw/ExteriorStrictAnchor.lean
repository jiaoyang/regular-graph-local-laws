import LocalLaw.ExteriorRate
import LocalLaw.EventualGraphMesh
import LocalLaw.SparseParameterAbsorption

/-!
# Strict exterior seeds for the actual graph bootstrap

The cavity exterior estimate is absorbed into half of the actual paper error
on a bounded exterior annulus. Every numerical side condition is realized
uniformly for sufficiently large N. The exceptional-center count and its
exponent restriction remain explicit geometric assumptions.
-/

open Filter

namespace LocalLaw

noncomputable section
local instance exteriorStrictDecidable (p : Prop) : Decidable p := Classical.propDecidable p

namespace RegularGraph
variable {N d : ℕ}

/-- Finite quantitative strict anchor on a bounded exterior annulus. All
normalization, localization, and logarithmic absorption budgets are explicit. -/
theorem exterior_strict_anchor (g : RegularGraph N d) (hN : 0 < N) (hd : 3 ≤ d)
    (a r R : ℕ) (hR : r + 1 ≤ R) (z : ℂ) (hzIm : 0 < z.im)
    (hz : 2 * (d : ℝ) ≤ ‖z‖) (B : ℝ) (hB : 0 ≤ B) (hzB : ‖z‖ ≤ B)
    (hlog : 1 ≤ Real.log (N : ℝ))
    (hlocal : 1 / (((d : ℝ) - 1) ^ r) ≤ 1 / (2 * (B + 2)))
    (hbad : ((nonTreeCenters g.graph R).card : ℝ) / (N : ℝ) ≤
      1 / (((d : ℝ) - 1) ^ r))
    (hinflate : 2 * (3 + 6 * (B + 2)) * Real.sqrt (2 * B + 3) ≤
      Real.log (N : ℝ) ^ (8 * a))
    (hentry : 2 ≤ Real.log (N : ℝ) ^ (8 * a))
    (hsmall : graphPaperError a d N r z ≤ 1) :
    (graphLocalLawFamily N d a r).strict z g := by
  let δ := 1 / (((d : ℝ) - 1) ^ r)
  let ε := graphPaperError a d N r z
  let C := 3 + 6 * (B + 2)
  let A := Real.sqrt (2 * B + 3)
  have hdR : (3 : ℝ) ≤ d := Nat.cast_le.mpr hd
  have hkpos : 0 < (d : ℝ) - 1 := by linarith
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hC : 0 ≤ C := by dsimp [C]; linarith
  have hA : 0 < A := by dsimp [A]; positivity
  have hε0 : 0 ≤ ε := graphPaperError_nonnegative a d N r z (by omega) hzIm.le
  have hfloor : Real.log (N : ℝ) ^ (8 * a) * δ ≤ ε := by
    have hh := graphPaperError_lower a d N r z hlog hzIm.le
    simpa only [localizationErrorFloor, Nat.cast_sub (by omega : 1 ≤ d),
      Nat.cast_one, ← one_div] using hh
  have hroot : 0 < Real.sqrt (spectralScale z + ε) :=
    Real.sqrt_pos.mpr (add_pos_of_pos_of_nonneg (spectralScale_pos hzIm) hε0)
  have hcap : Real.sqrt (spectralScale z + ε) ≤ A := by
    apply Real.sqrt_le_sqrt
    have hs := spectralScale_le_twice_norm_add_two z
    change spectralScale z + graphPaperError a d N r z ≤ 2 * B + 3
    linarith
  have hbudget : C * δ ≤ scalarScale (spectralScale z) ε / 2 := by
    have h₁ : 2 * C * δ ≤ (Real.log (N : ℝ) ^ (8 * a) * δ) / A := by
      apply (le_div_iff₀ hA).mpr
      convert mul_le_mul_of_nonneg_right hinflate hδ using 1
      dsimp [C, A]
      ring
    have h₂ : (Real.log (N : ℝ) ^ (8 * a) * δ) / A ≤ scalarScale (spectralScale z) ε := by
      exact div_le_div₀ hε0 hfloor hroot hcap
    linarith
  change ‖g.Q z - semicircleRoot z‖ ≤ scalarScale (spectralScale z) ε / 2 ∧
    ∀ i j, ‖g.G z i j - g.P r z (g.Q z) i j‖ ≤ ε / 2
  constructor
  · have hq := g.Q_exterior_anchor hN hd r R hR z hzIm hz B hzB hlocal
    have hq' : ‖g.Q z - semicircleRoot z‖ ≤ C * δ := by
      exact hq.trans ((add_le_add_left (mul_le_mul_of_nonneg_right hbad (by norm_num)) _).trans_eq (by dsimp [C, δ]; ring))
    exact hq'.trans hbudget
  · intro i j
    have hentryBudget : δ ≤ ε / 2 := by
      have hh := (mul_le_mul_of_nonneg_right hentry hδ).trans hfloor
      linarith
    exact (g.exterior_Q_reference_approximation hN hd r z hz i j).trans hentryBudget

end RegularGraph

/-- The actual logarithmic localization radius eventually satisfies every
fixed positive localization budget. -/
theorem eventually_exterior_localization_small (d : ℕ) (β B : ℝ)
    (hd : 3 ≤ d) (hβ : 0 < β) (hB : 0 ≤ B) :
    ∀ᶠ N : ℕ in atTop,
      1 / (((d : ℝ) - 1) ^ logarithmicRadius β d N) ≤ 1 / (2 * (B + 2)) := by
  filter_upwards [eventually_localization_log_budget β d 1 hβ hd,
    eventually_log_ge_nat (2 * (B + 2))] with N hlocal hlog
  have hlocal' : 1 / (((d : ℝ) - 1) ^ logarithmicRadius β d N) ≤
      1 / (3 * Real.log (N : ℝ)) := by
    simpa only [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one, ← one_div, pow_one] using hlocal
  exact hlocal'.trans (one_div_le_one_div_of_le (by positivity) (by linarith))

/-- Uniform actual strict bootstrap seeds on every bounded exterior annulus.
Only the polynomial count of non-tree centers and its compatible exponent
remain as geometric inputs. The structural radius R is arbitrary. -/
theorem eventually_exterior_strict_anchor (a b d : ℕ) (β γ B : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hβ : 0 < β)
    (hexp : γ + β ≤ 1) (hB : 0 ≤ B) :
    ∀ᶠ N : ℕ in atTop, ∀ (g : RegularGraph N d) (R : ℕ),
      logarithmicRadius β d N + 1 ≤ R →
      ((nonTreeCenters g.graph R).card : ℝ) ≤ (N : ℝ) ^ γ →
      ∀ z : ℂ, 2 * (d : ℝ) ≤ ‖z‖ → ‖z‖ ≤ B →
        Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
          (graphLocalLawFamily N d a (logarithmicRadius β d N)).strict z g := by
  let C := 2 * (3 + 6 * (B + 2)) * Real.sqrt (2 * B + 3)
  filter_upwards [eventually_ge_atTop 1, eventually_log_ge_nat (max 3 C),
    eventually_exterior_localization_small d β B hd hβ hB,
    eventually_paperError_small a b d β ha hb hd hβ] with N hN hlog hlocal herror
  intro g R hR hbad z hz hzB hheight
  have hNpos : 0 < N := by omega
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr hNpos
  have hlog3 : 3 ≤ Real.log (N : ℝ) := (le_max_left _ _).trans hlog
  have hlog1 : 1 ≤ Real.log (N : ℝ) := by linarith
  have hzIm : 0 < z.im := (div_pos (pow_pos (by linarith) _) hNp).trans_le hheight
  have hlogPow : Real.log (N : ℝ) ≤ Real.log (N : ℝ) ^ (8 * a) := by
    simpa only [pow_one] using pow_le_pow_right₀ hlog1 (show 1 ≤ 8 * a by omega)
  have hinflate : C ≤ Real.log (N : ℝ) ^ (8 * a) :=
    ((le_max_right _ _).trans hlog).trans hlogPow
  have hdensity := sparse_density_le_localization N d β γ
    (nonTreeCenters g.graph R).card hN hd hβ.le hexp hbad
  have hdensity' : ((nonTreeCenters g.graph R).card : ℝ) / (N : ℝ) ≤
      1 / (((d : ℝ) - 1) ^ logarithmicRadius β d N) := by
    simpa only [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one, ← one_div] using hdensity
  have herror' : graphPaperError a d N (logarithmicRadius β d N) z ≤
      (Real.log (N : ℝ) ^ (4 * a))⁻¹ := herror z hzIm hheight
  have hsmall : graphPaperError a d N (logarithmicRadius β d N) z ≤ 1 :=
    herror'.trans ((inv_le_one₀ (pow_pos (by linarith) _)).mpr (one_le_pow₀ hlog1))
  exact g.exterior_strict_anchor hNpos hd a _ R hR z hzIm hz B hB hzB hlog1
    hlocal hdensity' hinflate (by linarith) hsmall

end
end LocalLaw
