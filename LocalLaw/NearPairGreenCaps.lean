import LocalLaw.SourceGuardedCaps

/-! # All-vertex local Green caps require only diagonal and edge comparisons

An adjacent pair neighborhood lies in one ball of radius r+1. No reference
class for an arbitrary two-target union is asserted.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance nearPairGreenCapsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ}

theorem near_green_caps_of_pair_approximation (g : RegularGraph N d) (hd : 3 ≤ d)
    (r R : ℕ) (hmargin : r + 1 ≤ R)
    (hballs : ∀ v, graphBallExcess g.graph v R ≤ finiteOmega d)
    (z q : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) (B E : ℝ) {Edeleted : ℝ} (hB : ‖z‖ ≤ B)
    (S : SourceLocalCapBounds d r z q B E Edeleted)
    (hnear : ∀ i j, (i = j ∨ g.graph.Adj i j) → ‖g.G z i j - g.P r z q i j‖ ≤ E) :
    (∀ i j, (i = j ∨ g.graph.Adj i j) → ‖g.G z i j‖ ≤ sourceGreenEntryCap d) ∧
      (∀ i, ‖(g.G z i i)⁻¹‖ ≤ sourceGreenPivotCap d B) := by
  constructor
  · intro i j hij
    let M := g.pairModel i j r
    have hM : M.graph.Connected := pairBall_connected_of_eq_or_adjacent g.graph i j r hij
    have hbudget := g.local_pairModel_base_budget r R hmargin hballs i j hij
    have happ : ‖g.G z i j - M.extensionGreen q z (pairBallLeft g.graph i j r) (pairBallRight g.graph i j r)‖ ≤ E := by
      rw [g.pairModel_P]
      exact hnear i j hij
    exact M.base_reference_approximation_entry_cap hd hM hbudget z q hz hq (4 * r + 1)
      (pairBall_distance_bound g.graph i j r) S.diameter_feedback _ _ _ _ happ S.full_error S.change
  · intro i
    let M := g.pairModel i i r
    have hM : M.graph.Connected := pairBall_connected_of_eq_or_adjacent g.graph i i r (Or.inl rfl)
    have hbudget := g.local_pairModel_base_budget r R hmargin hballs i i (Or.inl rfl)
    have happ : ‖g.G z i i - M.extensionGreen q z (pairBallLeft g.graph i i r) (pairBallLeft g.graph i i r)‖ ≤ E := by
      change ‖g.G z i i - M.extensionGreen q z (pairBallLeft g.graph i i r) (pairBallRight g.graph i i r)‖ ≤ E
      rw [g.pairModel_P]
      exact hnear i i (Or.inl rfl)
    exact M.base_reference_approximation_pivot_cap hd hM hbudget z q hz hq B hB (4 * r + 1)
      (pairBall_distance_bound g.graph i i r) S.diameter_feedback _ _ _ happ S.full_pivot

end RegularGraph
end LocalLaw
