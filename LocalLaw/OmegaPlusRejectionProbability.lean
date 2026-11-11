import LocalLaw.SurgerySamplingCounts

/-! # Arbitrary polynomial rejection control under actual structural-plus

The pair sampling radius is R/2+1, so its two-root tree failures are charged
at radius R/2+2 <= R. Thus the literal bad-center clause of Omega-plus is
sufficient; no offset count or full-radius excess premise is introduced.
-/

noncomputable section
set_option maxHeartbeats 1800000
namespace LocalLaw
local instance omegaPlusRejectionDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def sourceRejectionConstant (Cq q : ℕ) : ℕ :=
  3 * Cq + 2 * (q - 1) * (Cq + 2) + 2 * q * (2 * (q - 1) + 1) + (q - 1)

namespace RegularGraph

theorem eventually_structuralPlus_rejection_probability (a d p : ℕ) (c γ : ℝ)
    (hd : 3 ≤ d) (hc : 0 < c) (hc₁ : c < 1) (hγ : γ < 1) :
    ∃ q : ℕ, 1 ≤ q ∧ ∀ᶠ N : ℕ in Filter.atTop,
      ∀ (g : RegularGraph N d) (o : Fin N) (ell ω Cq : ℕ), ell ≤ doubleLogRadius a d N →
      g.SourceStructuralPlus (logarithmicRadius (c / 4) d N) ω Cq ⌊(N : ℝ) ^ γ⌋₊ →
      eventMass (localSamplingWeight g.graph (graphBallVertices g.graph o ell))
        (fun S => sourceRejectionConstant Cq q <
          (rejectedResamplingIndices g.graph (graphBallVertices g.graph o ell)
            (logarithmicRadius (c / 4) d N / 4) S).card) ≤ 1 / (N : ℝ) ^ p := by
  let γ' := (γ + 1) / 2
  have hγ' : γ' < 1 := by dsimp [γ']; linarith
  have hgap : 0 < γ' - γ := by dsimp [γ']; linarith
  obtain ⟨q, hq, hnum⟩ := eventually_geometric_sampling_budget a d (p + 1) c γ' hc₁ hγ'
  refine ⟨q, hq, ?_⟩
  filter_upwards [hnum, eventually_resampling_ball_budget a d hd,
    eventually_resampling_radius_margin a d 4 4 (c / 4) hd (by linarith),
    eventually_log_ge_nat 1, Filter.eventually_ge_atTop 4,
    eventually_const_mul_log_rpow_le 2 0 (γ' - γ) hgap] with N hnum hball hmargin hlog hN htwo
  intro g o ell ω Cq hell hstruct
  let R := logarithmicRadius (c / 4) d N
  let M := R / 2 + 1
  let T := graphBallVertices g.graph o ell
  let μ : ℝ := Nat.card (BoundaryOrientedEdge g.graph T)
  let V : ℝ := (((d + 1) * (d - 1) ^ M : ℕ) : ℝ)
  let b : ℕ := 2 * ⌊(N : ℝ) ^ γ⌋₊
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hfit : ell + 1 + R / 4 ≤ R / 2 := by dsimp only [R]; omega
  have hMR : M + 1 ≤ R := by dsimp only [M, R]; omega
  have hsel : R / 4 ≤ M := by dsimp only [M]; omega
  have hsep : 2 * (R / 4) + 1 ≤ M := by dsimp only [M]; omega
  have hT : 4 * Nat.card T ≤ N := by
    apply (Nat.mul_le_mul_left 4 ((g.ball_card_bound o ell).trans
      (Nat.pow_le_pow_right (by omega : 0 < d + 1) hell))).trans hball
  have hbad : (nonTreeCenters g.graph (M + 1)).card ≤ b :=
    (Finset.card_le_card (nonTreeCenters_mono g.graph hMR)).trans hstruct.2.2
  have hμ : μ ≤ (d : ℝ) * ((d : ℝ) + 1) * Real.log (N : ℝ) ^ (2 * a) :=
    g.boundary_card_log_bound o a ell hd hlog hell
  have hV : V ≤ ((d : ℝ) + 1) * (N : ℝ) ^ (c / 4) := by
    have hm : M ≤ R := by omega
    have hmono : (d + 1) * (d - 1) ^ M ≤ (d + 1) * (d - 1) ^ R :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega : 0 < d - 1) hm)
    have hrpow := logarithmicRadius_power_bound (c / 4) d N (by linarith) hd (by omega)
    apply (Nat.cast_le.mpr hmono).trans
    dsimp only [R] at *
    push_cast
    exact mul_le_mul_of_nonneg_left hrpow (by positivity)
  have hb : (b : ℝ) ≤ (N : ℝ) ^ γ' := by
    have hfloor := Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) γ)
    have htwo' : (2 : ℝ) ≤ (N : ℝ) ^ (γ' - γ) := by simpa using htwo
    calc
      (b : ℝ) ≤ 2 * (N : ℝ) ^ γ := by dsimp only [b]; push_cast; nlinarith
      _ ≤ (N : ℝ) ^ (γ' - γ) * (N : ℝ) ^ γ :=
        mul_le_mul_of_nonneg_right htwo' (Real.rpow_nonneg hn.le _)
      _ = (N : ℝ) ^ γ' := by rw [← Real.rpow_add hn]; congr 1; ring
  have hfinite := g.localSampling_surgerySamplingGood_failure T M (q - 1) (q - 1) q (q - 1) b
    (by omega) hd hT hbad
  have hexp : q - 1 + 1 = q := Nat.sub_add_cancel hq
  rw [hexp] at hfinite
  have hbudget := hnum μ V (b : ℝ) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hμ hV hb
  have hcover : ∀ S, sourceRejectionConstant Cq q <
      (rejectedResamplingIndices g.graph T (R / 4) S).card →
      ¬SurgerySamplingGood g.graph T M (q - 1) (q - 1) q (q - 1) S := by
    intro S hbad hgood
    have hc := rejected_resampling_count_of_surgerySamplingGood g.graph o ell R M Cq (q - 1) (q - 1) q
      (q - 1) hfit hsel hsep (hstruct.2.1 o) S hgood
    exact Nat.not_lt_of_ge hc hbad
  have hmass := (eventMass_mono (localSamplingWeight g.graph T) finiteUniformWeight_nonneg hcover).trans
    (hfinite.trans hbudget)
  apply hmass.trans
  apply (div_le_div_iff₀ (pow_pos hn _) (pow_pos hn _)).mpr
  rw [pow_succ]
  nlinarith [mul_le_mul_of_nonneg_right (show (4 : ℝ) ≤ N by exact_mod_cast hN)
    (pow_nonneg hn.le p)]

end RegularGraph
end LocalLaw
