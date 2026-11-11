import LocalLaw.SourceGreenCaps
import LocalLaw.CavityAveragePerturbation
import LocalLaw.SparseParameterAbsorption

/-!
# Actual exceptional cavity bounds from the weak source event

The genuine Schur formula bounds each cavity term from full Green and inverse
pivot caps. The actual cavity iteration is uniformly bounded by its proved
closed formula. Consequently even exceptional centers have a fixed error cap.
-/

open scoped BigOperators
namespace LocalLaw
noncomputable section
local instance sourceCavityCapsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem cavity_iterate_norm_le_three (m z w : ℂ) (n : ℕ)
    (hm : m ^ 2 + z * m + 1 = 0) (hmnorm : ‖m‖ ≤ 1)
    (hsmall : (n : ℝ) * ‖w - m‖ ≤ 1 / 2) (hδ : ‖w - m‖ ≤ 1) :
    ‖cavityIterate z w n‖ ≤ 3 := by
  have hden := (cavityDenominator_bounds hmnorm n hsmall).1
  have hdenp : 0 < ‖cavityDenominator m (w - m) n‖ := by linarith
  have hnum : ‖m ^ (2 * n) * (w - m)‖ ≤ ‖w - m‖ := by
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hmnorm)
  have hfrac : ‖m ^ (2 * n) * (w - m) / cavityDenominator m (w - m) n‖ ≤ 2 * ‖w - m‖ := by
    rw [norm_div]
    apply (div_le_iff₀ hdenp).mpr
    nlinarith [mul_le_mul_of_nonneg_right hden (norm_nonneg (w - m))]
  rw [cavity_iterate_exact_of_small hm hmnorm n hsmall]
  exact (norm_add_le _ _).trans (by linarith)

noncomputable def sourceCavityCap (d : ℕ) (B : ℝ) : ℝ :=
  sourceGreenEntryCap d + sourceGreenEntryCap d ^ 2 * sourceGreenPivotCap d B

noncomputable def sourceExceptionalCavityCap (d : ℕ) (B : ℝ) : ℝ := sourceCavityCap d B + 3

theorem sourceExceptionalCavityCap_nonnegative (d : ℕ) (hd : 3 ≤ d) (B : ℝ) (hB : 0 ≤ B) :
    0 ≤ sourceExceptionalCavityCap d B := by
  have hC := finiteReferenceConstant_ge_one d hd
  unfold sourceExceptionalCavityCap sourceCavityCap sourceGreenEntryCap sourceGreenPivotCap
  positivity

namespace RegularGraph
variable {N d : ℕ}

/-- Actual centered cavity values inherit a cap from actual full Green/pivots. -/
theorem cavityAtVertex_norm_le_caps (g : RegularGraph N d) (hd : 0 < d) (z : ℂ) (hz : 0 < z.im)
    (C L : ℝ) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hG : ∀ i j, ‖g.G z i j‖ ≤ C) (hGi : ∀ j, ‖(g.G z j j)⁻¹‖ ≤ L) (i : Fin N) :
    ‖cavityAtVertex g.graph d z i‖ ≤ C + C ^ 2 * L := by
  have hpoint : ∀ j, ‖orientedCavity g.graph d z i j‖ ≤
      if g.graph.Adj i j then C + C ^ 2 * L else 0 := by
    intro j
    rw [orientedCavity_eq_matrixCavityTerm g.graph d z hz]
    split_ifs
    · exact matrixCavityTerm_norm_bound (g.G z) C L hC hL hG hGi i j
    · simp
  have hsum : (∑ j : Fin N, if g.graph.Adj i j then C + C ^ 2 * L else 0) =
      (d : ℝ) * (C + C ^ 2 * L) := by
    calc
      _ = (∑ j : Fin N, if g.graph.Adj i j then (1 : ℝ) else 0) * (C + C ^ 2 * L) := by
        rw [Finset.sum_mul]
        simp
      _ = _ := by
        rw [← g.graph.degree_eq_sum_if_adj (R := ℝ)]
        have hh := g.regular i
        simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hh ⊢
        rw [hh]
  unfold cavityAtVertex
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (d : ℝ)⁻¹ * ∑ j, ‖orientedCavity g.graph d z i j‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (d : ℝ)⁻¹ * ∑ j, if g.graph.Adj i j then C + C ^ 2 * L else 0 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => hpoint j)) (by positivity)
    _ = _ := by rw [hsum]; field_simp

/-- The exceptional-value bound needed by cavity averaging is now a theorem
on the actual weak source event; it holds at every center. -/
theorem eventually_sourceOmega_exceptional_cavity_cap (a b d : ℕ) (c β B : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hc : 0 < c)
    (hβ : 0 < β) (hβc : β ≤ c / 32) (hB : 0 ≤ B) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (z : ℂ) (badCount : ℕ),
      0 < z.im → ‖z‖ ≤ B → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
      g.SourceOmega a (logarithmicRadius β d N) (logarithmicRadius (c / 4) d N)
        (finiteOmega d) badCount z →
      ∀ i, ‖cavityAtVertex g.graph d z i - cavityIterate z (g.Q z) (actualCavityDepth a d N z)‖ ≤
        sourceExceptionalCavityCap d B := by
  filter_upwards [eventually_sourceOmega_green_caps a b d c β B ha hb hd hc hβ hβc hB,
    eventually_actual_cavity_parameters a b d β ha hb hd hβ,
    eventually_paperError_small a b d β ha hb hd hβ,
    eventually_log_ge_nat 1, Filter.eventually_ge_atTop 1] with N hcaps hparameters herror hlog hN
  intro g z badCount hz hzB hscale hOmega i
  have hG := hcaps g z badCount hz hzB hscale hOmega
  have hC : 0 ≤ sourceGreenEntryCap d := by
    have hh := finiteReferenceConstant_ge_one d hd
    unfold sourceGreenEntryCap
    linarith
  have hL : 0 ≤ sourceGreenPivotCap d B := by
    have hh := finiteReferenceConstant_ge_one d hd
    unfold sourceGreenPivotCap
    positivity
  have hcv := g.cavityAtVertex_norm_le_caps (by omega) z hz _ _ hC hL hG.1 hG.2 i
  have hprior : ‖g.Q z - semicircleRoot z‖ ≤ scalarScale (spectralScale z)
      (graphPaperError a d N (logarithmicRadius β d N) z) := hOmega.2.1
  have he := herror z hz hscale
  have hε : 0 ≤ graphPaperError a d N (logarithmicRadius β d N) z :=
    graphPaperError_nonnegative _ _ _ _ _ hN hz.le
  have hlogp : 0 < Real.log (N : ℝ) := by linarith
  have hεone : graphPaperError a d N (logarithmicRadius β d N) z ≤ 1 :=
    he.trans ((inv_le_one₀ (pow_pos hlogp _)).mpr (one_le_pow₀ hlog))
  have hscaleone : scalarScale (spectralScale z) (graphPaperError a d N (logarithmicRadius β d N) z) ≤ 1 :=
    (scalarScale_le_sqrt (spectralScale_pos hz) hε).trans
      (Real.sqrt_le_iff.mpr ⟨by norm_num, by simpa using hεone⟩)
  have hsmall := (hparameters z hz hscale).2.2.2
  have hsmall' : (actualCavityDepth a d N z : ℝ) * ‖g.Q z - semicircleRoot z‖ ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left hprior (Nat.cast_nonneg _)).trans hsmall
  have hiter := cavity_iterate_norm_le_three (semicircleRoot z) z (g.Q z) _
    (semicircleRoot_equation z) (semicircleRoot_norm_le_one z) hsmall' (hprior.trans hscaleone)
  exact (norm_sub_le _ _).trans (by
    change ‖cavityAtVertex g.graph d z i‖ + ‖cavityIterate z (g.Q z) (actualCavityDepth a d N z)‖ ≤
      (sourceGreenEntryCap d + sourceGreenEntryCap d ^ 2 * sourceGreenPivotCap d B) + 3
    linarith)

end RegularGraph
end
end LocalLaw
