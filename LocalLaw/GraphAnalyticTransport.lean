import LocalLaw.CavityContinuity
import LocalLaw.BoundaryResolvent
import LocalLaw.GraphTheorem42
import LocalLaw.BranchTransport

/-!
# Actual graph observables in the spectral-transport argument

The analytic continuity constants for G, Q, m and P(z,Q(z)) are proved for
the physical regular-graph model. A remaining base-error modulus controls
which same-branch net comparisons satisfy the relative error budgets.
-/

noncomputable section

namespace LocalLaw

local instance graphTransportDecidable (p : Prop) : Decidable p := Classical.propDecidable p

namespace RegularGraph

variable {N d : ℕ}

theorem pairBoundaryCoefficient_le_two (g : RegularGraph N d) (hd : 3 ≤ d)
    (i j : Fin N) (r : ℕ) (v : pairBallVertices g.graph i j r) :
    g.pairBoundaryCoefficient i j r v ≤ 2 := by
  have hdc : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hden : (0 : ℝ) < (d : ℝ) - 1 := by linarith
  unfold pairBoundaryCoefficient
  apply (div_le_iff₀ hden).mpr
  have hdeg : (0 : ℝ) ≤ ((pairBallGraph g.graph i j r).degree v : ℝ) := Nat.cast_nonneg _
  linarith

/-- The full local boundary model is coarsely continuous at its actual Q
parameter. This requires no bounded-excess or local-law assumption. -/
theorem P_Q_lipschitz (g : RegularGraph N d) (hN : 0 < N) (hd : 3 ≤ d)
    (r : ℕ) (z w : ℂ) (η₀ : ℝ) (hη : 0 < η₀)
    (hz : η₀ ≤ z.im) (hw : η₀ ≤ w.im) (i j : Fin N) :
    ‖g.P r z (g.Q z) i j - g.P r w (g.Q w) i j‖ ≤
      ((1 + 2 / η₀ ^ 2) / η₀ ^ 2) * dist z w := by
  have hzp := hη.trans_le hz
  have hwp := hη.trans_le hw
  have hb := boundaryGreen_entry_lipschitz
    (normalizedAdjacency (pairBallGraph g.graph i j r) d)
    (normalizedAdjacency_isHermitian _ d)
    (g.pairBoundaryCoefficient i j r) (g.pairBoundaryCoefficient_nonnegative hd i j r)
    2 (by norm_num) (g.pairBoundaryCoefficient_le_two hd i j r)
    (g.Q z) (g.Q w) z w η₀ hη hz hw
    (g.Q_im_nonnegative z hzp) (g.Q_im_nonnegative w hwp)
    (pairBallLeft g.graph i j r) (pairBallRight g.graph i j r)
  have hq := g.Q_lipschitz hN (by omega) z w η₀ hη hz hw
  have hqdist : dist (g.Q z) (g.Q w) ≤ (1 / η₀ ^ 2) * dist z w := by
    simpa only [dist_eq_norm] using hq
  change ‖g.P r z (g.Q z) i j - g.P r w (g.Q w) i j‖ ≤ _ at hb
  calc
    _ ≤ (dist z w + 2 * dist (g.Q z) (g.Q w)) / η₀ ^ 2 := hb
    _ ≤ (dist z w + 2 * ((1 / η₀ ^ 2) * dist z w)) / η₀ ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      linarith
    _ = ((1 + 2 / η₀ ^ 2) / η₀ ^ 2) * dist z w := by ring

end RegularGraph

/-- The actual analytic family used by the paper, including its explicit
thresholded error rather than an independent placeholder function. -/
noncomputable def graphLocalLawFamily (N d a r : ℕ) : LocalLawFamily (RegularGraph N d) (Fin N) where
  Q g z := g.Q z
  G g z := g.G z
  P g z w := g.P r z w
  m := semicircleRoot
  s := spectralScale
  ε := graphPaperError a d N r

/-- Source-specific local transport from proved analytic bounds and explicit
budget comparisons. No event inclusion or continuity of epsilon is assumed. -/
noncomputable def graphTransportStep (N d a r : ℕ) (hN : 0 < N) (hd : 3 ≤ d)
    (structural : RegularGraph N d → Prop) (z w : ℂ) (η₀ : ℝ)
    (hη : 0 < η₀) (hz : η₀ ≤ z.im) (hw : η₀ ≤ w.im)
    (cavityBudget : scalarScale (spectralScale w) (graphPaperError a d N r w) / 2 +
      (1 / η₀ ^ 2 + 1 / η₀) * dist z w ≤
        scalarScale (spectralScale z) (graphPaperError a d N r z))
    (entryBudget : graphPaperError a d N r w / 2 +
      (1 / η₀ ^ 2 + ((1 + 2 / η₀ ^ 2) / η₀ ^ 2)) * dist z w ≤
        graphPaperError a d N r z) :
    LocalLawTransportStep (graphLocalLawFamily N d a r) structural w z := by
  apply LocalLawTransportStep.ofComponents (graphLocalLawFamily N d a r) structural w z
    (1 / η₀ ^ 2) (1 / η₀) (1 / η₀ ^ 2) ((1 + 2 / η₀ ^ 2) / η₀ ^ 2)
    (by positivity) (by positivity) (by positivity) (by positivity)
  · intro g _
    exact g.Q_lipschitz hN (by omega) z w η₀ hη hz hw
  · have hm := semicircleRoot_lipschitz (z := z) (w := w) η₀ hη hz hw
    change ‖semicircleRoot z - semicircleRoot w‖ ≤ _
    calc
      _ ≤ ‖z - w‖ / η₀ := hm
      _ = (1 / η₀) * dist z w := by rw [dist_eq_norm]; ring
  · intro g _ i j
    exact green_entry_lipschitz_universal g.H g.H_hermitian z w η₀ hη hz hw i j
  · intro g _ i j
    exact g.P_Q_lipschitz hN hd r z w η₀ hη hz hw i j
  · exact cavityBudget
  · exact entryBudget

end LocalLaw
