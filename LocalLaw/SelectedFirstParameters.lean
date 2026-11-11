import LocalLaw.SelectedFirstGreen
import LocalLaw.SourceSurgeryParameters
import LocalLaw.SharpSamplingCounts

/-!
# Realized selected-first inverse row bounds

The true selected block is close to its own physical diagonal. Source
approximation, pair separation and guarded pivots supply every matrix input;
the actual boundary size and nominal error realize its contraction.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2200000
namespace LocalLaw
local instance selectedFirstParametersDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph

theorem eventually_selectedFirstGreen_inverse_rows (a b d : ℕ) (c β B C1 : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hc : 0 < c)
    (hβ : 0 < β) (hβc : β ≤ c / 32) (hC1 : 0 ≤ C1) (hB : 0 ≤ B) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0 < z.im → ‖z‖ ≤ B → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im → ∀ Cq badCount : ℕ,
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c / 4) d N) (actualCavityDepth a d N z - 1)
        (finiteOmega d) Cq badCount C1 o z →
      ∀ {ι : Type} [Fintype ι]
      (boundary : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1))),
      let T := graphBallVertices g.graph o (actualCavityDepth a d N z - 1)
      let selector := logarithmicRadius (c / 4) d N / 4
      let s := g.admissibleState T boundary samples
      ∀ i : s.AdmissibleSampleIndex selector,
        ∑ j, ‖(s.selectedFirstGreen selector d z)⁻¹ i j‖ ≤ 2 * sourceGreenPivotCap d B := by
  let P := sourceGreenPivotCap d B
  let U := (d : ℝ) * ((d : ℝ) + 1)
  have hP : 0 ≤ P := by
    have hC := finiteReferenceConstant_ge_one d hd
    dsimp only [P, sourceGreenPivotCap]
    positivity
  have hU : 0 ≤ U := by dsimp only [U]; positivity
  have hdepth := (lowerLogLogRadius_tendsto a d (by omega) hd).eventually (Filter.eventually_ge_atTop 4)
  filter_upwards [eventually_actualGuardedDeletionCaps a b d c β C1 B ha hb hd hc hβ hβc hC1 hB,
    eventually_paperError_small a b d β ha hb hd hβ,
    eventually_effectiveModelRadius_common_ball_margin a d c β hd hc hβ hβc,
    eventually_log_ge_nat 1, eventually_log_ge_nat (2 * (U * (P * C1))),
    hdepth, Filter.eventually_ge_atTop 1]
    with N hcaps herror hmargin hlog hlarge hdepth hN
  intro g o z hz hzB hscale Cq badCount hplus ι _ boundary samples
  dsimp only
  let ell := actualCavityDepth a d N z - 1
  let R := logarithmicRadius (c / 4) d N
  let selector := R / 4
  let r := effectiveModelRadius a d N β
  let T := graphBallVertices g.graph o ell
  let s := g.admissibleState T boundary samples
  let n := Fintype.card (s.AdmissibleSampleIndex selector)
  let L := Real.log (N : ℝ)
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  let δ := C1 * g.sourcePrime a (logarithmicRadius β d N) z
  have hε : 0 ≤ ε := graphPaperError_nonnegative a d N _ z hN hz.le
  have hLp : 0 < L := by dsimp only [L]; linarith
  have hδ : 0 ≤ δ := by unfold δ sourcePrime inflatedPrime; positivity
  have hcap : ε * L ^ (4 * a) ≤ 1 := (le_div_iff₀ (pow_pos hLp _)).mp
    (by simpa only [one_div] using herror z hz hscale)
  have hell : ell ≤ doubleLogRadius a d N := (actualCavityDepth_radius_bounds a d N z hdepth).2
  have hn : n ≤ Nat.card (BoundaryOrientedEdge g.graph T) := by
    have hh : Fintype.card (s.AdmissibleSampleIndex selector) ≤ Fintype.card ι := Fintype.card_subtype_le _
    exact hh.trans_eq (by simpa only [Nat.card_eq_fintype_card] using Fintype.card_congr boundary)
  have hcount : (n : ℝ) ≤ U * L ^ (2 * a) :=
    (Nat.cast_le.mpr hn).trans (g.boundary_card_log_bound o a ell hd hlog hell)
  have hs := source_endpoint_surgery_smallness a L ε (n : ℝ) U 0 1 (P * C1)
    (by omega) hlog hε hU (by norm_num) (by norm_num) (mul_nonneg hP hC1)
      hcap hcount (by simpa only [mul_zero, zero_mul, zero_add, add_zero, one_mul, mul_one] using hlarge)
  have hsmall : P * (n : ℝ) * δ ≤ 1 / 2 := by
    convert hs using 1
    unfold δ sourcePrime inflatedPrime
    ring
  have hsep : 2 * r + 1 ≤ selector := by dsimp only [r, selector, R]; omega
  have hselector : 1 ≤ selector := by dsimp only [selector, R]; omega
  have happrox : ∀ x y, ‖(g.deficient.delete T).G z x y - (g.deficient.delete T).P r z (g.Q z) x y‖ ≤ δ :=
    hplus.deleted
  have hoff := g.selectedFirstGreen_offdiagonal_of_pair_approximation hd T boundary samples selector r
    hsep (g.Q z) z hz (g.Q_im_nonnegative z hz) δ happrox
  have hpivot := g.selectedFirstGreen_pivot_of_guardedCaps T boundary samples selector hselector z
    (guardedGreenEntryCap d) P (hcaps g o z hz hzB hscale Cq badCount hplus)
  exact s.selectedFirstGreen_inverse_rows selector d z hz P δ hP hδ hpivot hoff hsmall

end RegularGraph
end LocalLaw
