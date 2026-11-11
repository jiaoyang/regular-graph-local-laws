import LocalLaw.L2FiniteProjection
import LocalLaw.SelfAdjointResolventLimit

/-! # Actual finite-coordinate graph truncations converge strongly -/

open scoped BigOperators Topology ENNReal
open Filter LocalLaw
noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
namespace SimpleGraph
local instance graphDirichletOperatorLimitDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [G.LocallyFinite]

def finiteDirichletRestriction (S : Finset V) : SimpleGraph V where
  Adj v w := v∈S ∧ w∈S ∧ G.Adj v w
  symm := fun _ _ h => ⟨h.2.1,h.1,G.symm h.2.2⟩
  loopless := fun v h => G.loopless v h.2.2

instance finiteDirichletRestrictionLocallyFinite (S : Finset V) : (G.finiteDirichletRestriction S).LocallyFinite :=
  fun v => Fintype.ofInjective (fun w : (G.finiteDirichletRestriction S).neighborSet v =>
    (⟨w.val,w.property.2.2⟩ : G.neighborSet v))
    (fun _ _ h => Subtype.ext (congrArg (fun w : G.neighborSet v => w.val) h))

omit [DecidableEq V] in
theorem finiteDirichletRestriction_degree_le (S : Finset V) (v : V) :
    (G.finiteDirichletRestriction S).degree v≤G.degree v := by
  have h := Nat.card_le_card_of_injective (fun w : (G.finiteDirichletRestriction S).neighborSet v =>
    (⟨w.val,w.property.2.2⟩ : G.neighborSet v))
    (fun _ _ h => Subtype.ext (congrArg (fun w : G.neighborSet v => w.val) h))
  simpa only [←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using h

theorem finiteDirichletRestriction_neighborFinset (S : Finset V) (v : V) :
    (G.finiteDirichletRestriction S).neighborFinset v=if v∈S then G.neighborFinset v∩S else ∅ := by
  ext w
  simp only [SimpleGraph.mem_neighborFinset,finiteDirichletRestriction]
  by_cases hv : v∈S <;> simp [hv,and_comm,and_left_comm,and_assoc]

theorem finiteDirichletRestriction_adjacency_factor (S : Finset V) (D : ℕ) (hD : ∀ v,G.degree v≤D) :
    (G.finiteDirichletRestriction S).boundedAdjacency D
      (fun v => (G.finiteDirichletRestriction_degree_le S v).trans (hD v))=
      (l2FiniteProjection S).comp ((G.boundedAdjacency D hD).comp (l2FiniteProjection S)) := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext v
  simp only [ContinuousLinearMap.comp_apply,boundedAdjacency_apply,l2FiniteProjection_apply,
    G.finiteDirichletRestriction_neighborFinset]
  by_cases hv : v∈S
  · rw [if_pos hv,if_pos hv]
    rw [←Finset.sum_filter]
    congr 1
  · simp only [hv,if_false,Finset.sum_empty]

theorem finiteDirichletRestriction_adjacency_tendsto (S : ℕ → Finset V) (hmono : Monotone S)
    (hcover : ∀ v,∃ n,v∈S n) (D : ℕ) (hD : ∀ v,G.degree v≤D) (f : GraphL2 V) :
    Tendsto (fun n => (G.finiteDirichletRestriction (S n)).boundedAdjacency D
      (fun v => (G.finiteDirichletRestriction_degree_le (S n) v).trans (hD v)) f) atTop
      (𝓝 (G.boundedAdjacency D hD f)) := by
  let A := G.boundedAdjacency D hD
  let P := fun n => l2FiniteProjection (S n)
  have hP (u : GraphL2 V) : Tendsto (fun n => P n u) atTop (𝓝 u) := l2FiniteProjection_tendsto S hmono hcover u
  have hinner : Tendsto (fun n => A (P n f-f)) atTop (𝓝 0) := by
    have hsub : Tendsto (fun n => P n f-f) atTop (𝓝 0) := by
      simpa only [sub_self] using (hP f).sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => f) atTop (𝓝 f))
    simpa only [map_zero] using (A.continuous.tendsto 0).comp hsub
  have hfirst : Tendsto (fun n => P n (A (P n f-f))) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hh := squeeze_zero (fun n => norm_nonneg (P n (A (P n f-f))))
      (fun n => l2FiniteProjection_norm_le (S n) _) (by simpa only [norm_zero] using hinner.norm)
    exact hh
  have hsum := hfirst.add (hP (A f))
  have heq (n : ℕ) : P n (A (P n f-f))+P n (A f)=
      (G.finiteDirichletRestriction (S n)).boundedAdjacency D
        (fun v => (G.finiteDirichletRestriction_degree_le (S n) v).trans (hD v)) f := by
    rw [G.finiteDirichletRestriction_adjacency_factor (S n) D hD]
    change P n (A (P n f-f))+P n (A f)=P n (A (P n f))
    rw [map_sub,map_sub]
    abel
  have hsum' : Tendsto (fun n => P n (A (P n f-f))+P n (A f)) atTop (𝓝 (A f)) := by
    simpa only [zero_add] using hsum
  exact hsum'.congr' (Filter.Eventually.of_forall heq)

theorem finiteDirichletRestriction_normalized_tendsto (S : ℕ → Finset V) (hmono : Monotone S)
    (hcover : ∀ v,∃ n,v∈S n) (d : ℕ) (hD : ∀ v,G.degree v≤d) (f : GraphL2 V) :
    Tendsto (fun n => (G.finiteDirichletRestriction (S n)).normalizedOperator d
      (fun v => (G.finiteDirichletRestriction_degree_le (S n) v).trans (hD v)) f) atTop
      (𝓝 (G.normalizedOperator d hD f)) := by
  have h := (G.finiteDirichletRestriction_adjacency_tendsto S hmono hcover d hD f).const_smul
    (Real.sqrt ((d:ℝ)-1))⁻¹
  exact h

/-- Strong finite Dirichlet graph exhaustion converges to the actual bounded
operator resolvent on ell2, for every upper-half-plane spectral parameter. -/
theorem finiteDirichletRestriction_resolvents_tendsto (S : ℕ → Finset V) (hmono : Monotone S)
    (hcover : ∀ v,∃ n,v∈S n) (d : ℕ) (hD : ∀ v,G.degree v≤d) (z : ℂ) (hz : 0<z.im) (f : GraphL2 V) :
    Tendsto (fun n => (G.finiteDirichletRestriction (S n)).infiniteGreenOperator d
      (fun v => (G.finiteDirichletRestriction_degree_le (S n) v).trans (hD v)) z f) atTop
      (𝓝 (G.infiniteGreenOperator d hD z f)) :=
  selfAdjoint_resolvents_tendsto_strong (G.normalizedOperator d hD) (G.normalizedOperator_selfAdjoint d hD)
    (fun n => (G.finiteDirichletRestriction (S n)).normalizedOperator d
      (fun v => (G.finiteDirichletRestriction_degree_le (S n) v).trans (hD v)))
    (fun n => (G.finiteDirichletRestriction (S n)).normalizedOperator_selfAdjoint d _)
    (G.finiteDirichletRestriction_normalized_tendsto S hmono hcover d hD) z hz f

theorem finiteDirichletRestriction_Green_tendsto (S : ℕ → Finset V) (hmono : Monotone S)
    (hcover : ∀ v,∃ n,v∈S n) (d : ℕ) (hD : ∀ v,G.degree v≤d) (z : ℂ) (hz : 0<z.im) (i j : V) :
    Tendsto (fun n => (G.finiteDirichletRestriction (S n)).infiniteGreen d
      (fun v => (G.finiteDirichletRestriction_degree_le (S n) v).trans (hD v)) z i j) atTop
      (𝓝 (G.infiniteGreen d hD z i j)) := by
  have hcoe := (lp.uniformContinuous_coe (E:=fun _ : V => ℂ) (p:=2)).continuous
  have heval := (continuous_apply i).comp hcoe
  exact heval.continuousAt.tendsto.comp (G.finiteDirichletRestriction_resolvents_tendsto S hmono hcover d hD z hz
    (lp.single 2 j 1))

end SimpleGraph
