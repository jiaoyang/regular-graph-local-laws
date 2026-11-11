import LocalLaw.CavityDeletionBounds
import LocalLaw.SwitchingQParameters

/-!
# Source-scale absorption of the physical deletion bias

The actual removed ball has quadratic cost O((log N)^(4a)). The fractional
error component absorbs that cost, uniformly in the spectral parameter, with
sixteen inverse logarithmic powers to spare. Actual Green and pivot caps are
the remaining analytic inputs to this deterministic bias comparison.
-/

open scoped BigOperators
namespace LocalLaw
noncomputable section
local instance cavityDeleteParameterDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def deletionQConstant (d : ℕ) (B C L : ℝ) : ℝ :=
  (1 + C * L) ^ 2 * C * deletionInverseEntryCap d B C + 2 * B * (C + C ^ 2 * L)

theorem deletionInverseEntryCap_nonnegative (d : ℕ) (B C : ℝ) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    0 ≤ deletionInverseEntryCap d B C := by unfold deletionInverseEntryCap; positivity

theorem deletionQConstant_nonnegative (d : ℕ) (B C L : ℝ)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hL : 0 ≤ L) : 0 ≤ deletionQConstant d B C L := by
  unfold deletionQConstant
  have := deletionInverseEntryCap_nonnegative d B C hB hC
  positivity

theorem deletion_Q_budget_le (N d t : ℕ) (B C L η : ℝ)
    (hN : 0 < N) (hd : 3 ≤ d) (_hB : 0 ≤ B) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hη : 0 < η) (hηB : η ≤ B) :
    ((N : ℝ) * (d : ℝ))⁻¹ *
      ((((d : ℝ) * (1 + C * L) ^ 2 * C / η) *
        ((t : ℝ) ^ 2 * deletionInverseEntryCap d B C)) +
          (2 * (d : ℝ) * (t : ℝ)) * (C + C ^ 2 * L)) ≤
      deletionQConstant d B C L * (t : ℝ) ^ 2 / ((N : ℝ) * η) := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hdp : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
  have ht : (t : ℝ) ≤ (t : ℝ) ^ 2 := by
    have hh : (t : ℝ) ≤ (t : ℝ) * (t : ℝ) := by exact_mod_cast (Nat.le_mul_self t)
    simpa only [pow_two] using hh
  have hM : 0 ≤ C + C ^ 2 * L := by positivity
  have hlast : 2 * (t : ℝ) * (C + C ^ 2 * L) * η ≤
      2 * B * (C + C ^ 2 * L) * (t : ℝ) ^ 2 := by
    calc
      _ ≤ 2 * (t : ℝ) ^ 2 * (C + C ^ 2 * L) * B := by gcongr
      _ = _ := by ring
  apply (le_div_iff₀ (mul_pos hn hη)).mpr
  have heq : (((N : ℝ) * (d : ℝ))⁻¹ *
      ((((d : ℝ) * (1 + C * L) ^ 2 * C / η) *
        ((t : ℝ) ^ 2 * deletionInverseEntryCap d B C)) +
          (2 * (d : ℝ) * (t : ℝ)) * (C + C ^ 2 * L))) * ((N : ℝ) * η) =
      (1 + C * L) ^ 2 * C * deletionInverseEntryCap d B C * (t : ℝ) ^ 2 +
        2 * (t : ℝ) * (C + C ^ 2 * L) * η := by field_simp; ring
  rw [heq]
  unfold deletionQConstant
  nlinarith

/-- The source error absorbs any fixed quadratic ball cost with the actual
logarithmic exponent. -/
theorem deletion_change_absorption (ℓ X ε t K M δ : ℝ) (a b : ℕ)
    (hℓ : 1 ≤ ℓ) (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hX : 0 < X)
    (hε : 0 ≤ ε) (ht : 0 ≤ t) (hK : 0 ≤ K) (_hM : 0 ≤ M)
    (hmargin : K * M ^ 2 ≤ ℓ)
    (hsample : ℓ ^ b ≤ X) (hfraction : ℓ ^ (8 * a) / X ^ (2 / 3 : ℝ) ≤ ε)
    (htbound : t ≤ M * ℓ ^ (2 * a)) (hδ : δ ≤ K * t ^ 2 / X) : δ ≤ ε / ℓ ^ 16 := by
  have hℓp : 0 < ℓ := by linarith
  have hlower := fractional_component_sample_lower ℓ X ε a b hℓ hX hε hfraction hsample (by omega)
  have hpow : ℓ ^ (4 * a + 17) ≤ ℓ ^ (12 * a + 4) := pow_le_pow_right₀ hℓ (by omega)
  have ht2 : t ^ 2 ≤ M ^ 2 * ℓ ^ (4 * a) := by
    have hh := pow_le_pow_left₀ ht htbound 2
    have heq : (M * ℓ ^ (2 * a)) ^ 2 = M ^ 2 * ℓ ^ (4 * a) := by
      rw [mul_pow, ← pow_mul, show 2 * a * 2 = 4 * a by omega]
    rwa [heq] at hh
  have hscaled : K * t ^ 2 * ℓ ^ 16 ≤ ε * X := by
    calc
      _ ≤ (K * (M ^ 2 * ℓ ^ (4 * a))) * ℓ ^ 16 := by gcongr
      _ = (K * M ^ 2) * ℓ ^ (4 * a + 16) := by rw [pow_add]; ring
      _ ≤ ℓ * ℓ ^ (4 * a + 16) := mul_le_mul_of_nonneg_right hmargin (by positivity)
      _ = ℓ ^ (4 * a + 17) := by rw [show 4 * a + 17 = (4 * a + 16) + 1 by omega, pow_succ]; ring
      _ ≤ ε * X := hpow.trans hlower
  apply hδ.trans
  apply (div_le_iff₀ hX).mpr
  apply (mul_le_mul_right (pow_pos hℓp 16)).mp
  calc
    _ ≤ ε * X := hscaled
    _ = (ε / ℓ ^ 16 * X) * ℓ ^ 16 := by field_simp

namespace RegularGraph
variable {N d : ℕ}

theorem ball_card_log_bound (g : RegularGraph N d) (o : Fin N) (a ell : ℕ)
    (hd : 3 ≤ d) (hL : 1 ≤ Real.log (N : ℝ)) (hell : ell ≤ doubleLogRadius a d N) :
    (Nat.card (graphBallVertices g.graph o ell) : ℝ) ≤
      ((d : ℝ) + 1) * Real.log (N : ℝ) ^ (2 * a) := by
  have hn : (Nat.card (graphBallVertices g.graph o ell) : ℝ) ≤
      ((d : ℝ) + 1) * (((d - 1 : ℕ) : ℝ) ^ ell) := by exact_mod_cast (g.ball_card_sharp o ell hd)
  have hk : (1 : ℝ) ≤ ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ d - 1 by omega)
  exact hn.trans (mul_le_mul_of_nonneg_left
    ((pow_le_pow_right₀ hk hell).trans (doubleLogRadius_base_power_bound a d N hd hL)) (by positivity))

/-- Actual Q versus the outside-edge cavity sum at every allowed source
radius. No removed-set size, inverse-block estimate or bias estimate is a
premise; only the physical entry and pivot caps remain. -/
theorem eventually_ball_Q_outside_cavity_bias_small (a b d : ℕ) (B C L : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hL : 0 ≤ L) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (ell r : ℕ) (z : ℂ),
      ell ≤ doubleLogRadius a d N → 0 < z.im → ‖z‖ ≤ B →
      Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
      (∀ i j, ‖g.G z i j‖ ≤ C) → (∀ j, ‖(g.G z j j)⁻¹‖ ≤ L) →
      (∀ i j, ‖green (normalizedAdjacency (outsideGraph g.graph (graphBallVertices g.graph o ell)) d) z i j‖ ≤ C) →
      (∀ j, ‖(green (normalizedAdjacency (outsideGraph g.graph (graphBallVertices g.graph o ell)) d) z j j)⁻¹‖ ≤ L) →
      ‖g.Q z - ((N : ℝ) * (d : ℝ))⁻¹ •
        ∑ e : OutsideOrientedEdge g.graph (graphBallVertices g.graph o ell),
          outsideOrientedCavityValue g.graph d (graphBallVertices g.graph o ell) z e‖ ≤
            graphPaperError a d N r z / Real.log (N : ℝ) ^ 16 := by
  let K := deletionQConstant d B C L
  have hK : 0 ≤ K := deletionQConstant_nonnegative d B C L hB hC hL
  filter_upwards [eventually_log_ge_nat 1, eventually_log_ge_nat (K * ((d : ℝ) + 1) ^ 2),
    Filter.eventually_ge_atTop 1] with N hlog hmargin hN
  intro g o ell r z hell hz hzB hscale hR hRi hS hSi
  let T := graphBallVertices g.graph o ell
  have hI : ∀ i, (g.G z i i).im ≤ C := fun i =>
    ((le_abs_self _).trans (Complex.abs_im_le_norm _)).trans (hR i i)
  have hraw := g.Q_outside_cavity_average_difference T z hz C L C hC hL hR hRi hS hSi hI
  have hmass := g.physical_retained_inverse_mass_bound T z hz B C hzB hC hS
  have hfinite := deletion_Q_budget_le N d (Nat.card T) B C L z.im (by omega) hd hB hC hL hz
    (((le_abs_self _).trans (Complex.abs_im_le_norm _)).trans hzB)
  have hδ : ‖g.Q z - ((N : ℝ) * (d : ℝ))⁻¹ •
        ∑ e : OutsideOrientedEdge g.graph T, outsideOrientedCavityValue g.graph d T z e‖ ≤
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

end RegularGraph
end
end LocalLaw
