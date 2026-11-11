import LocalLaw.SourceEndpointApproximation

/-! # Weak source errors retained at their sharp logarithmic order

The comparison is to an actual finite restriction. The direct pair error
is C1*epsilon and the proved localization cost is O(L*epsilon); no extra
logarithmic powers are introduced when summing over a full modified block.
-/

noncomputable section
namespace LocalLaw
local instance sharpSourceRestrictionDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace DeficientGraph
variable {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] {d : ℕ}

omit [Fintype I] in
theorem source_weak_restriction_approximation (g : DeficientGraph V d)
    (hd : 3 ≤ d) (S : Set V) (e : I ↪ S) (r R : ℕ) (z q : ℂ)
    (hz : 0 < z.im) (hq : 0 ≤ q.im) (B C1 ε L A : ℝ) (hB : ‖z‖ ≤ B)
    (num : SourceObservationBounds d r z B C1 ε L A)
    (hbudget : (g.restrict S).ComponentFiniteReferenceBudget)
    (hdiam : ∀ x y, (g.restrict S).graph.dist x y ≤ R)
    (hRlog : (R : ℝ) + 1 ≤ A * L)
    (hcapture : ∀ i, graphBallVertices g.graph (e i).val r ⊆ S)
    (hprior : ‖q - semicircleRoot z‖ ≤ C1 * scalarScale (spectralScale z) ε)
    (hpair : ∀ i j, ‖g.G z (e i).val (e j).val - g.P r z q (e i).val (e j).val‖ ≤ C1 * ε) :
    ∀ i j, ‖g.G z (e i).val (e j).val - (g.restrict S).extensionGreen q z (e i) (e j)‖ ≤
      (C1 + localizationWeakConstant d B A * C1 ^ 2 * L) * ε := by
  let M := g.restrict S
  have hscaled : 0 ≤ C1 ^ 2 * ε := mul_nonneg (sq_nonneg C1) num.error_nonnegative
  have hprior' := hprior.trans (scalarScale_constant_absorption (spectralScale z) ε C1
    (spectralScale_pos hz) num.error_nonnegative num.coefficient_one)
  intro i j
  have hlocal := M.componentwise_weak_pair_localization hd hbudget q z hz hq B hB
    (C1 ^ 2 * ε) L A hscaled num.log_one num.log_cap_nonnegative num.error_scaled hprior'
    R r hdiam hRlog num.pair_log num.localization_large num.tail (e i) (e j)
  have hid := g.restrict_pair_P S (e i) (e j) r (hcapture i) (hcapture j) q z
  rw [hid] at hlocal
  have hreverse : ‖g.P r z q (e i).val (e j).val - M.extensionGreen q z (e i) (e j)‖ ≤
      localizationWeakConstant d B A * L * (C1 ^ 2 * ε) := by
    simpa only [norm_sub_rev] using hlocal
  exact ((norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
    (add_le_add (hpair i j) hreverse)).trans_eq (by ring)

end DeficientGraph
end LocalLaw
