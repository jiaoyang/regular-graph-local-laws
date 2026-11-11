import LocalLaw.L2FiniteProjection
import LocalLaw.SelfAdjointResolventLimit

/-! # Genuine graph resolvents under eventual local agreement

All graphs live on one ambient vertex set. Uniformly bounded degree and
eventual equality of each finite neighbor set imply strong convergence of
the actual adjacency operators, hence convergence of genuine Green entries.
No convergence of resolvents is assumed.
-/

open Filter
open scoped BigOperators Topology ENNReal
noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
namespace SpectralConsequences
open LocalLaw
local instance localGraphLimitDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*} [DecidableEq V]

theorem bounded_operators_strong_of_eventual_single
    (A : GraphL2 V →L[ℂ] GraphL2 V) (An : ℕ → GraphL2 V →L[ℂ] GraphL2 V)
    (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ f, ‖A f‖ ≤ C * ‖f‖) (hAn : ∀ n f, ‖An n f‖ ≤ C * ‖f‖)
    (hsingle : ∀ v a, ∀ᶠ n : ℕ in atTop, An n (lp.single 2 v a) = A (lp.single 2 v a))
    (f : GraphL2 V) : Tendsto (fun n => An n f) atTop (𝓝 (A f)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hsum : Tendsto (fun S : Finset V => l2FiniteProjection S f) atTop (𝓝 f) :=
    lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) f
  have happrox := (Metric.tendsto_nhds.mp hsum) (ε / (2 * (C + 1))) (by positivity)
  obtain ⟨S, hS⟩ := happrox.exists
  have hsmall : ‖f - l2FiniteProjection S f‖ < ε / (2 * (C + 1)) := by
    simpa only [dist_eq_norm, norm_sub_rev] using hS
  have hfinite : ∀ᶠ n : ℕ in atTop, An n (l2FiniteProjection S f) = A (l2FiniteProjection S f) := by
    have hall : ∀ᶠ n : ℕ in atTop, ∀ v ∈ S, An n (lp.single 2 v (f v)) = A (lp.single 2 v (f v)) :=
      (Filter.eventually_all_finset S).mpr (fun v _ => hsingle v (f v))
    filter_upwards [hall] with n hn
    change An n (∑ v ∈ S, lp.single 2 v (f v)) = A (∑ v ∈ S, lp.single 2 v (f v))
    simp only [map_sum]
    exact Finset.sum_congr rfl (fun v hv => hn v hv)
  filter_upwards [hfinite] with n hn
  have hid : An n f - A f = An n (f - l2FiniteProjection S f) - A (f - l2FiniteProjection S f) := by
    rw [map_sub, map_sub, hn]
    abel
  have hb : ‖An n f - A f‖ ≤ 2 * C * ‖f - l2FiniteProjection S f‖ := by
    rw [hid]
    exact (norm_sub_le _ _).trans (by nlinarith [hAn n (f-l2FiniteProjection S f), hA (f-l2FiniteProjection S f)])
  have hc : 2 * C * ‖f - l2FiniteProjection S f‖ < ε := by
    have hlt := (lt_div_iff₀ (by positivity : 0 < 2 * (C+1))).mp hsmall
    nlinarith [norm_nonneg (f-l2FiniteProjection S f)]
  simpa only [dist_eq_norm] using hb.trans_lt hc

variable (G : SimpleGraph V) [G.LocallyFinite]
    (Gn : ℕ → SimpleGraph V) [∀ n, (Gn n).LocallyFinite]

theorem adjacency_strong_of_neighbor_agreement (d : ℕ)
    (hG : ∀ v, G.degree v ≤ d) (hGn : ∀ n v, (Gn n).degree v ≤ d)
    (hlocal : ∀ v, ∀ᶠ n : ℕ in atTop, (Gn n).neighborFinset v = G.neighborFinset v)
    (f : GraphL2 V) :
    Tendsto (fun n => (Gn n).boundedAdjacency d (hGn n) f) atTop
      (𝓝 (G.boundedAdjacency d hG f)) := by
  apply bounded_operators_strong_of_eventual_single _ _ (d : ℝ) (Nat.cast_nonneg d)
  · exact G.adjacencyLp_norm_bound d hG
  · intro n
    exact (Gn n).adjacencyLp_norm_bound d (hGn n)
  · intro v a
    filter_upwards [hlocal v] with n hn
    apply lp.ext
    funext w
    rw [(Gn n).boundedAdjacency_single, G.boundedAdjacency_single]
    have he : (Gn n).Adj w v ↔ G.Adj w v := by
      rw [(Gn n).adj_comm, G.adj_comm]
      rw [← (Gn n).mem_neighborFinset, hn, G.mem_neighborFinset]
    simp only [he]

theorem normalized_strong_of_neighbor_agreement (d : ℕ)
    (hG : ∀ v, G.degree v ≤ d) (hGn : ∀ n v, (Gn n).degree v ≤ d)
    (hlocal : ∀ v, ∀ᶠ n : ℕ in atTop, (Gn n).neighborFinset v = G.neighborFinset v)
    (f : GraphL2 V) :
    Tendsto (fun n => (Gn n).normalizedOperator d (hGn n) f) atTop
      (𝓝 (G.normalizedOperator d hG f)) := by
  simpa only [SimpleGraph.normalizedOperator, ContinuousLinearMap.smul_apply] using
    (adjacency_strong_of_neighbor_agreement G Gn d hG hGn hlocal f).const_smul
      (Real.sqrt ((d : ℝ)-1))⁻¹

theorem resolvents_strong_of_neighbor_agreement (d : ℕ)
    (hG : ∀ v, G.degree v ≤ d) (hGn : ∀ n v, (Gn n).degree v ≤ d)
    (hlocal : ∀ v, ∀ᶠ n : ℕ in atTop, (Gn n).neighborFinset v = G.neighborFinset v)
    (z : ℂ) (hz : 0 < z.im) (f : GraphL2 V) :
    Tendsto (fun n => (Gn n).infiniteGreenOperator d (hGn n) z f) atTop
      (𝓝 (G.infiniteGreenOperator d hG z f)) :=
  selfAdjoint_resolvents_tendsto_strong (G.normalizedOperator d hG)
    (G.normalizedOperator_selfAdjoint d hG)
    (fun n => (Gn n).normalizedOperator d (hGn n))
    (fun n => (Gn n).normalizedOperator_selfAdjoint d (hGn n))
    (normalized_strong_of_neighbor_agreement G Gn d hG hGn hlocal) z hz f

theorem green_tendsto_of_neighbor_agreement (d : ℕ)
    (hG : ∀ v, G.degree v ≤ d) (hGn : ∀ n v, (Gn n).degree v ≤ d)
    (hlocal : ∀ v, ∀ᶠ n : ℕ in atTop, (Gn n).neighborFinset v = G.neighborFinset v)
    (z : ℂ) (hz : 0 < z.im) (i j : V) :
    Tendsto (fun n => (Gn n).infiniteGreen d (hGn n) z i j) atTop
      (𝓝 (G.infiniteGreen d hG z i j)) := by
  have heval := (continuous_apply i).comp (lp.uniformContinuous_coe (E := fun _ : V => ℂ) (p := 2)).continuous
  exact heval.continuousAt.tendsto.comp
    (resolvents_strong_of_neighbor_agreement G Gn d hG hGn hlocal z hz (lp.single 2 j 1))

end SpectralConsequences
