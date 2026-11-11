import LocalLaw.SourceSpectralEvents

/-!
# Source local improvement implies the proved bootstrap certificate

The actual inside-ball distance controls its second decay denominator.
The average absolute cavity estimate controls the norm of the genuine
neighbor average. Thus the source OmegaMinusLocal event supplies the exact
certificate used by scalar closure; its own Q prior is not needed here.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw

local instance sourceCertificateDecidable (p : Prop) : Decidable p := Classical.propDecidable p

namespace RegularGraph

variable {N d : ℕ}

theorem cavityAtVertex_eq_neighbor_average (g : RegularGraph N d) (o : Fin N) (z : ℂ) :
    cavityAtVertex g.graph d z o = (d : ℂ)⁻¹ * ∑ j : g.graph.neighborSet o,
      green (deletedMatrix g.H j.val) z ⟨o, j.property.ne⟩ ⟨o, j.property.ne⟩ := by
  have hsplit := Fintype.sum_subtype_add_sum_subtype (fun j : Fin N => g.graph.Adj o j)
    (fun j => orientedCavity g.graph d z o j)
  have hzero : (∑ j : {j : Fin N // ¬ g.graph.Adj o j}, orientedCavity g.graph d z o j.val) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    simp [orientedCavity, j.property]
  have hsum : (∑ j : g.graph.neighborSet o, orientedCavity g.graph d z o j.val) =
      ∑ j : Fin N, orientedCavity g.graph d z o j := by
    simpa only [hzero, add_zero] using hsplit
  unfold cavityAtVertex
  rw [← hsum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have hadj : g.graph.Adj o j.val := j.property
  dsimp only [orientedCavity]
  rw [dif_pos hadj.ne, if_pos hadj]
  rfl

/-- The triangle inequality consumes the source average of absolute errors;
the desired norm bound is not assumed separately. -/
theorem sourceCavityResidual_norm_bound (g : RegularGraph N d) (hd : 0 < d)
    (ell : ℕ) (o : Fin N) (z : ℂ) :
    ‖cavityAtVertex g.graph d z o - cavityIterate z (g.Q z) (ell + 1)‖ ≤
      g.sourceCavityAbsoluteResidual ell o z := by
  let f : g.graph.neighborSet o → ℂ := fun j =>
    green (deletedMatrix g.H j.val) z ⟨o, j.property.ne⟩ ⟨o, j.property.ne⟩
  let Y := cavityIterate z (g.Q z) (ell + 1)
  have hcard : Fintype.card (g.graph.neighborSet o) = d :=
    (g.graph.card_neighborSet_eq_degree o).trans (g.regular o)
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)
  have hmean : cavityAtVertex g.graph d z o - Y = (d : ℂ)⁻¹ * ∑ j, (f j - Y) := by
    rw [g.cavityAtVertex_eq_neighbor_average]
    change (d : ℂ)⁻¹ * ∑ j, f j - Y = _
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
    field_simp [hdC]
  change ‖cavityAtVertex g.graph d z o - Y‖ ≤ (d : ℝ)⁻¹ * ∑ j, ‖f j - Y‖
  rw [hmean, norm_mul, norm_inv, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr (Nat.cast_nonneg _))

/-- Membership in the actual finite ball gives its actual finite distance
bound, including possibly disconnected ambient graphs. -/
theorem sourceInside_distance_le (g : RegularGraph N d) (o i : Fin N) (ell : ℕ)
    (hi : i ∈ graphBallVertices g.graph o ell) : (g.graph.edist o i).toNat ≤ ell := by
  change g.graph.edist o i ≤ (ell : ℕ∞) at hi
  have hne := ne_top_of_le_ne_top (ENat.coe_ne_top ell) hi
  have heq := ENat.coe_toNat hne
  exact ENat.coe_le_coe.mp (heq.symm ▸ hi)

end RegularGraph

theorem resamplingDecayDenominator_eq_rpow (d ell : ℕ) :
    resamplingDecayDenominator d ell = ((d - 1 : ℕ) : ℝ) ^ ((ell : ℝ) / 2) := by
  have hk : (0 : ℝ) ≤ ((d - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  unfold resamplingDecayDenominator
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hk]
  congr 1
  ring

namespace RegularGraph

variable {N d : ℕ}

theorem sourceInside_decayDenominator_le (g : RegularGraph N d) (hd : 3 ≤ d)
    (o i : Fin N) (ell : ℕ) (hi : i ∈ graphBallVertices g.graph o ell) :
    resamplingDecayDenominator d ell ≤ ((d - 1 : ℕ) : ℝ) ^
      ((ell : ℝ) - ((g.graph.edist o i).toNat : ℝ) / 2) := by
  rw [resamplingDecayDenominator_eq_rpow d ell]
  have hdist : ((g.graph.edist o i).toNat : ℝ) ≤ ell :=
    Nat.cast_le.mpr (g.sourceInside_distance_le o i ell hi)
  apply Real.rpow_le_rpow_of_exponent_le
  · exact_mod_cast (show 1 ≤ d - 1 by omega)
  · linarith

theorem sourceInsideRowBudget_le_common (g : RegularGraph N d) (hd : 3 ≤ d)
    (a r ell : ℕ) (C2 : ℝ) (hC2 : 0 ≤ C2) (o i : Fin N) (z : ℂ)
    (hN : 1 ≤ N) (hz : 0 ≤ z.im) (hi : i ∈ graphBallVertices g.graph o ell) :
    g.sourceInsideRowBudget a r ell C2 o i z ≤
      C2 * (((Real.log (N : ℝ) / resamplingDecayDenominator d ell +
        Real.log (N : ℝ) ^ 2 / resamplingDecayDenominator d ell) * g.sourcePrime a r z) +
          Real.log (N : ℝ) * g.sourceFeedback z) := by
  have hD : 0 < resamplingDecayDenominator d ell := by
    unfold resamplingDecayDenominator
    apply Real.sqrt_pos.mpr
    exact pow_pos (Nat.cast_pos.mpr (by omega)) _
  have hden := g.sourceInside_decayDenominator_le hd o i ell hi
  have hquot := div_le_div_of_nonneg_left (sq_nonneg (Real.log (N : ℝ))) hD hden
  have hprime : 0 ≤ g.sourcePrime a r z := by
    unfold sourcePrime inflatedPrime
    exact mul_nonneg (pow_nonneg (Real.log_nonneg (by exact_mod_cast hN)) _)
      (graphPaperError_nonnegative a d N r z hN hz)
  unfold sourceInsideRowBudget
  exact mul_le_mul_of_nonneg_left
    (add_le_add_right (mul_le_mul_of_nonneg_right (add_le_add_left hquot _) hprime) _) hC2

namespace SourceOmegaMinusLocal

/-- The exact source local event yields the actual bootstrap certificate at
the selected depth and the constructed closure budget's concrete tolerances. -/
theorem certificate {a r R : ℕ} {C2 : ℝ} {o : Fin N} {z : ℂ} {g : RegularGraph N d}
    (h : g.SourceOmegaMinusLocal a r R (actualCavityDepth a d N z - 1) C2 o z)
    (ha : 12 ≤ a) (hd : 3 ≤ d) (hC2 : 0 ≤ C2)
    (hlog : 1 ≤ Real.log (N : ℝ)) (hconstant : 2 * C2 ≤ Real.log (N : ℝ) ^ 3)
    (hz : 0 < z.im) (D : ClosureBudget z (semicircleRoot z) (spectralScale z) (graphPaperError a d N r z))
    (hdepth : D.depth = actualCavityDepth a d N z)
    (hbase : D.rowBase = graphPaperError a d N r z / Real.log (N : ℝ))
    (hfeedback : D.rowFeedback = C2 * Real.log (N : ℝ))
    (hcavity : D.cavityError = graphPaperError a d N r z / (2 * Real.log (N : ℝ) ^ 2)) :
    CavityRowCertificate (g.Q z) (semicircleRoot z) z (spectralScale z)
      (graphPaperError a d N r z) D (g.G z) (fun w => g.P r z w)
      (cavityAtVertex g.graph d z) (nonTreeCenters g.graph R) o := by
  let ell := actualCavityDepth a d N z - 1
  let L := Real.log (N : ℝ)
  let ε := graphPaperError a d N r z
  have hN : 1 ≤ N := by have := o.isLt; omega
  have hnums := local_improvement_error_budgets L ε C2 (resamplingDecayDenominator d ell)
    hlog D.errorPositive.le hC2 (selected_radius_decay_gain a d N z ha hd hlog) hconstant
  have hn := (nonresonantDepth_bounds (semicircleRoot z) (baselineCavityDepth a d N)).1
  have hnpos : 1 ≤ actualCavityDepth a d N z := by
    change baselineCavityDepth a d N ≤ actualCavityDepth a d N z at hn
    unfold baselineCavityDepth at hn
    omega
  have hdepth' : D.depth = ell + 1 := by dsimp [ell]; omega
  constructor
  · intro hgood
    have htree : (graphBall g.graph o R).IsTree := by
      by_contra htree
      exact hgood ((nonTreeCenters_membership g.graph R o).mpr htree)
    rw [hcavity, hdepth']
    exact (g.sourceCavityResidual_norm_bound (by omega) ell o z).trans
      ((h.localCavity htree).trans hnums.2.2)
  · intro i
    rw [hbase, hfeedback]
    change ‖g.G z o i - g.P r z (g.Q z) o i‖ ≤ ε / L + (C2 * L) * g.sourceFeedback z
    by_cases hi : i ∈ graphBallVertices g.graph o ell
    · have hcommon := (h.rowInside i hi).trans
        (g.sourceInsideRowBudget_le_common hd a r ell C2 hC2 o i z
          hN hz.le hi)
      calc
        _ ≤ C2 * (((L / resamplingDecayDenominator d ell + L ^ 2 / resamplingDecayDenominator d ell) *
            g.sourcePrime a r z) + L * g.sourceFeedback z) := hcommon
        _ = C2 * ((L / resamplingDecayDenominator d ell + L ^ 2 / resamplingDecayDenominator d ell) *
            inflatedPrime L ε) + (C2 * L) * g.sourceFeedback z := by
              unfold sourcePrime
              ring
        _ ≤ _ := add_le_add_right hnums.1 _
    · have hrow := h.rowOutside i hi
      calc
        _ ≤ C2 * (L ^ 2 * g.sourcePrime a r z / resamplingDecayDenominator d ell +
            L * g.sourceFeedback z) := hrow
        _ = C2 * (L ^ 2 * inflatedPrime L ε / resamplingDecayDenominator d ell) +
            (C2 * L) * g.sourceFeedback z := by unfold sourcePrime; ring
        _ ≤ _ := add_le_add_right hnums.2.1 _

end SourceOmegaMinusLocal
end RegularGraph
end LocalLaw
