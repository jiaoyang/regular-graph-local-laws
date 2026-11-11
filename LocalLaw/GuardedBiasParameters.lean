import LocalLaw.GuardedOutsideMean
import LocalLaw.OutsideCavityBiasParameters
import LocalLaw.ResamplingStructuralCost

/-!
# Source-scale guarded deletion and far-mask density

The physical deletion bias is derived from local caps and outer-boundary
entries only. Rejected far masks have a negligible true sampling density.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance guardedBiasParametersDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ}

/-- Exactly the local physical data used by guarded cavity averaging. -/
structure GuardedDeletionCaps (g : RegularGraph N d) (T A : Set (Fin N))
    (z : ℂ) (C L : ℝ) : Prop where
  full_diagonal : ∀ i, ‖g.G z i i‖ ≤ C
  full_edge : ∀ i j, g.graph.Adj i j → ‖g.G z i j‖ ≤ C
  full_pivot : ∀ i, ‖(g.G z i i)⁻¹‖ ≤ L
  guarded_diagonal : ∀ i, ‖guardedDeletedGreen g.H T A z i i‖ ≤ C
  guarded_edge : ∀ i j, g.graph.Adj i j → ‖guardedDeletedGreen g.H T A z i j‖ ≤ C
  guarded_nonzero : ∀ i, guardedDeletedGreen g.H T A z i i ≠ 0
  guarded_pivot : ∀ i, ‖(guardedDeletedGreen g.H T A z i i)⁻¹‖ ≤ L
  boundary_entry : ∀ u v : (Tᶜ : Set (Fin N)),
    (∃ t : T, g.graph.Adj t.val u.val) → (∃ t : T, g.graph.Adj t.val v.val) →
    ‖green (normalizedAdjacency (outsideGraph g.graph T) d) z u v‖ ≤ C

theorem eventually_ball_Q_outside_guarded_bias_small (a b d : ℕ) (B C L : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hL : 0 ≤ L) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (ell r : ℕ) (A : Set (Fin N)) (z : ℂ),
      ell ≤ doubleLogRadius a d N → 0 < z.im → ‖z‖ ≤ B →
      Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
      (∀ i, ‖g.G z i i‖ ≤ C) →
      (∀ i j, g.graph.Adj i j → ‖g.G z i j‖ ≤ C) →
      (∀ j, ‖(g.G z j j)⁻¹‖ ≤ L) →
      (∀ i, ‖guardedDeletedGreen g.H (graphBallVertices g.graph o ell) A z i i‖ ≤ C) →
      (∀ i j, g.graph.Adj i j → ‖guardedDeletedGreen g.H (graphBallVertices g.graph o ell) A z i j‖ ≤ C) →
      (∀ i, guardedDeletedGreen g.H (graphBallVertices g.graph o ell) A z i i ≠ 0) →
      (∀ i, ‖(guardedDeletedGreen g.H (graphBallVertices g.graph o ell) A z i i)⁻¹‖ ≤ L) →
      (∀ u v : ((graphBallVertices g.graph o ell)ᶜ : Set (Fin N)),
        (∃ t : graphBallVertices g.graph o ell, g.graph.Adj t.val u.val) →
        (∃ t : graphBallVertices g.graph o ell, g.graph.Adj t.val v.val) →
        ‖green (normalizedAdjacency (outsideGraph g.graph (graphBallVertices g.graph o ell)) d) z u v‖ ≤ C) →
      ‖g.Q z - ((N : ℝ) * (d : ℝ))⁻¹ •
        ∑ e : OutsideOrientedEdge g.graph (graphBallVertices g.graph o ell),
          outsideMatrixCavityValue g.graph (graphBallVertices g.graph o ell)
            (guardedDeletedGreen g.H (graphBallVertices g.graph o ell) A z) e‖ ≤
            graphPaperError a d N r z / Real.log (N : ℝ) ^ 16 := by
  let K := deletionQConstant d B C L
  have hK : 0 ≤ K := deletionQConstant_nonnegative d B C L hB hC hL
  filter_upwards [eventually_log_ge_nat 1, eventually_log_ge_nat (K * ((d : ℝ) + 1) ^ 2),
    Filter.eventually_ge_atTop 1] with N hlog hmargin hN
  intro g o ell r A z hell hz hzB hscale hRd hRe hRi hSd hSe hSp hSi hS
  let T := graphBallVertices g.graph o ell
  have hI : ∀ i, (g.G z i i).im ≤ C := fun i =>
    ((le_abs_self _).trans (Complex.abs_im_le_norm _)).trans (hRd i)
  have hraw := g.Q_outside_guarded_cavity_average_difference T A z hz C L C hC hL hRd hRe hRi hSd hSe hSp hSi hI
  have hmass := g.physical_retained_inverse_mass_bound_on_boundary T z hz B C hzB hC hS
  have hfinite := deletion_Q_budget_le N d (Nat.card T) B C L z.im (by omega) hd hB hC hL hz
    (((le_abs_self _).trans (Complex.abs_im_le_norm _)).trans hzB)
  have hδ : ‖g.Q z - ((N : ℝ) * (d : ℝ))⁻¹ •
        ∑ e : OutsideOrientedEdge g.graph T, outsideMatrixCavityValue g.graph T (guardedDeletedGreen g.H T A z) e‖ ≤
      K * (Nat.card T : ℝ) ^ 2 / ((N : ℝ) * z.im) := by
    apply (hraw.trans _).trans hfinite
    gcongr
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  apply deletion_change_absorption (Real.log (N : ℝ)) ((N : ℝ) * z.im)
    (graphPaperError a d N r z) (Nat.card T : ℝ) K ((d : ℝ) + 1) _ a b
    hlog ha hb (by positivity) (graphPaperError_nonnegative _ _ _ _ _ hN hz.le)
    (Nat.cast_nonneg _) hK (by positivity) hmargin
    (by have hh := (div_le_iff₀ hn).mp hscale; simpa only [mul_comm] using hh)
    (graphPaperError_fractional_lower _ _ _ _ _ hlog hz.le)
    (g.ball_card_log_bound o a ell hd hlog hell) hδ

/-- The actual outside-edge mean has the same two logarithmic tolerances,
using only local caps, safe deleted pivots and outer-boundary entries. -/
theorem eventually_ball_guarded_cavity_mean_bias_small (a b d : ℕ) (B C L : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hL : 0 ≤ L) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (ell r : ℕ)
      (A : Set (Fin N)) (z : ℂ),
      ell ≤ doubleLogRadius a d N → 0 < z.im → ‖z‖ ≤ B →
      Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
      g.GuardedDeletionCaps (graphBallVertices g.graph o ell) A z C L →
      ‖g.Q z - finiteComplexMean (outsideMatrixCavityValue g.graph (graphBallVertices g.graph o ell)
        (guardedDeletedGreen g.H (graphBallVertices g.graph o ell) A z))‖ ≤
        2 * graphPaperError a d N r z / Real.log (N : ℝ) ^ 16 := by
  let M := C + C ^ 2 * L
  let K := 2 * B * M
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  filter_upwards [eventually_ball_Q_outside_guarded_bias_small a b d B C L ha hb hd hB hC hL,
    eventually_resampling_ball_budget a d hd, eventually_log_ge_nat 1,
    eventually_log_ge_nat (K * ((d : ℝ) + 1) ^ 2), Filter.eventually_ge_atTop 1]
    with N hraw hball hlog hmargin hN
  intro g o ell r A z hell hz hzB hscale caps
  let T := graphBallVertices g.graph o ell
  let f := outsideMatrixCavityValue g.graph T (guardedDeletedGreen g.H T A z)
  have hT : 4 * Nat.card T ≤ N := by
    apply (Nat.mul_le_mul_left 4 ((g.ball_card_bound o ell).trans
      (Nat.pow_le_pow_right (by omega : 0 < d + 1) hell))).trans hball
  have hcap : ∀ e, ‖f e‖ ≤ M :=
    outsideMatrixCavityValue_norm_bound g.graph T (guardedDeletedGreen g.H T A z) C L hC hL
      caps.guarded_diagonal caps.guarded_edge caps.guarded_pivot
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
  have hfirst := hraw g o ell r A z hell hz hzB hscale caps.full_diagonal caps.full_edge
    caps.full_pivot caps.guarded_diagonal caps.guarded_edge caps.guarded_nonzero caps.guarded_pivot caps.boundary_entry
  have htriangle := norm_sub_le_norm_sub_add_norm_sub (g.Q z)
    (((N : ℝ) * (d : ℝ))⁻¹ • ∑ e, f e) (finiteComplexMean f)
  have hsecond : ‖((N : ℝ) * (d : ℝ))⁻¹ • ∑ e, f e - finiteComplexMean f‖ ≤
      graphPaperError a d N r z / Real.log (N : ℝ) ^ 16 := by
    simpa only [norm_sub_rev] using hsmall
  exact htriangle.trans ((add_le_add hfirst hsecond).trans_eq (by ring))

end RegularGraph
end LocalLaw
