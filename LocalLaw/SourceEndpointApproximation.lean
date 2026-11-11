import LocalLaw.SourceSingletonObservation
import LocalLaw.PairRestrictionIdentity

/-!
# Actual old endpoint approximation in one finite surgery model

The common model is an actual restriction capturing the endpoint balls.
Its proved finite class and geometric diameter transport the source pair
errors to one genuine matrix. The scalar prior retains the nominal error.
-/

noncomputable section
namespace LocalLaw
local instance sourceEndpointApproxDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace DeficientGraph
variable {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] {d : ℕ}

omit [Fintype I] in
/-- No common-matrix endpoint approximation is assumed: it follows from
the actual pair errors, containment, finite class and scalar budgets. -/
theorem source_endpoint_restriction_approximation (g : DeficientGraph V d)
    (hd : 3 ≤ d) (S : Set V) (e : I ↪ S) (r R : ℕ) (z q : ℂ)
    (hz : 0 < z.im) (hq : 0 ≤ q.im) (B C1 ε L A : ℝ) (hB : ‖z‖ ≤ B)
    (num : SourceObservationBounds d r z B C1 ε L A)
    (hbudget : (g.restrict S).ComponentFiniteReferenceBudget)
    (hdiam : ∀ x y, (g.restrict S).graph.dist x y ≤ R)
    (hRlog : (R : ℝ) + 1 ≤ A * L)
    (hcapture : ∀ i, graphBallVertices g.graph (e i).val r ⊆ S)
    (hprior : ‖q - semicircleRoot z‖ ≤ C1 * scalarScale (spectralScale z) ε)
    (hpair : ∀ i j, ‖g.G z (e i).val (e j).val - g.P r z q (e i).val (e j).val‖ ≤ C1 * L ^ 3 * ε) :
    ∀ i j, ‖g.G z (e i).val (e j).val - (g.restrict S).extensionGreen q z (e i) (e j)‖ ≤
      2 * C1 * L ^ 3 * ε := by
  let M := g.restrict S
  let K := localizationWeakConstant d B A
  have hL : 0 ≤ L := (by norm_num : (0 : ℝ) ≤ 1).trans num.log_one
  have hε : 0 ≤ ε := num.error_nonnegative
  have hC : 0 ≤ C1 := (by norm_num : (0 : ℝ) ≤ 1).trans num.coefficient_one
  have hscaled : 0 ≤ C1 ^ 2 * ε := mul_nonneg (sq_nonneg C1) num.error_nonnegative
  have hprior' := hprior.trans (scalarScale_constant_absorption (spectralScale z) ε C1
    (spectralScale_pos hz) num.error_nonnegative num.coefficient_one)
  have hlocal (i j : I) : ‖M.extensionGreen q z (e i) (e j) - M.P r z q (e i) (e j)‖ ≤
      K * L * (C1 ^ 2 * ε) :=
    M.componentwise_weak_pair_localization hd hbudget q z hz hq B hB (C1 ^ 2 * ε) L A
      hscaled num.log_one num.log_cap_nonnegative num.error_scaled hprior' R r hdiam
      hRlog num.pair_log num.localization_large num.tail (e i) (e j)
  have hlocalbudget : K * L * (C1 ^ 2 * ε) ≤ C1 * L ^ 3 * ε := by
    calc
      _ = (K * C1) * (C1 * L * ε) := by ring
      _ ≤ L ^ 2 * (C1 * L * ε) := mul_le_mul_of_nonneg_right num.feedback_large (by positivity)
      _ = _ := by ring
  intro i j
  have hid := g.restrict_pair_P S (e i) (e j) r (hcapture i) (hcapture j) q z
  have hsecond : ‖g.P r z q (e i).val (e j).val - M.extensionGreen q z (e i) (e j)‖ ≤
      C1 * L ^ 3 * ε := by
    rw [← hid]
    have hh : ‖M.P r z q (e i) (e j) - M.extensionGreen q z (e i) (e j)‖ ≤
        K * L * (C1 ^ 2 * ε) := by simpa only [norm_sub_rev] using hlocal i j
    exact hh.trans hlocalbudget
  exact ((norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add (hpair i j) hsecond)).trans_eq (by ring)

end DeficientGraph
end LocalLaw
