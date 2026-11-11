import LocalLaw.FiniteResampling
import LocalLaw.GraphModel
import LocalLaw.LocalResamplingData

/-!
# Endpoint counting for uniform sampled edges

A bounded endpoint-fiber cardinality gives a probability bound by counting,
not by assuming the desired probability. The graph specialization injects each
outside-edge endpoint fiber into the ambient neighbor set. The remaining size
hypothesis on the outside oriented-edge set is the deterministic deletion-count
input in Proposition 5.9.
-/

open scoped BigOperators
noncomputable section

namespace LocalLaw

local instance endpointSamplingDecidable (p : Prop) : Decidable p := Classical.propDecidable p

section FiniteCounting

variable {Ω V : Type*} [Fintype Ω]

/-- Uniform event mass is exactly the favorable cardinality divided by the
sample cardinality. The identity remains defined for the empty sample type. -/
theorem uniform_eventMass_cardinality (P : Ω → Prop) :
    eventMass (finiteUniformWeight Ω) P =
      (Nat.card {ω // P ω} : ℝ) / (Fintype.card Ω : ℝ) := by
  classical
  rw [Nat.card_eq_fintype_card]
  unfold eventMass finiteUniformWeight
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, Fintype.card_subtype]
  ring

/- A set of endpoint values has at most its cardinality times the largest
endpoint-fiber cardinality many preimages. -/
theorem endpoint_preimage_card_bound (f : Ω → V) (B : Finset V) (d : ℕ)
    (hfiber : ∀ v, Nat.card {ω // f ω = v} ≤ d) :
    Nat.card {ω // f ω ∈ B} ≤ B.card * d := by
  classical
  let F : {ω // f ω ∈ B} → Σ v : B, {ω // f ω = v.val} :=
    fun ω => ⟨⟨f ω.val, ω.property⟩, ⟨ω.val, rfl⟩⟩
  have hF : Function.Injective F := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun x : Σ v : B, {ω // f ω = v.val} => x.2.val) hab
  calc
    Nat.card {ω // f ω ∈ B} ≤ Nat.card (Σ v : B, {ω // f ω = v.val}) :=
      Nat.card_le_card_of_injective F hF
    _ = ∑ v : B, Nat.card {ω // f ω = v.val} := Nat.card_sigma
    _ ≤ ∑ _v : B, d := Finset.sum_le_sum (fun v _ => hfiber v.val)
    _ = B.card * d := by simp

/-- The exact uniform endpoint-set bound used before taking a graph-size
lower bound. No probability conclusion is assumed. -/
theorem uniform_endpoint_set_bound (f : Ω → V) (B : Finset V) (d : ℕ)
    (hfiber : ∀ v, Nat.card {ω // f ω = v} ≤ d) :
    eventMass (finiteUniformWeight Ω) (fun ω => f ω ∈ B) ≤
      (d : ℝ) * (B.card : ℝ) / (Fintype.card Ω : ℝ) := by
  rw [uniform_eventMass_cardinality]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have h := endpoint_preimage_card_bound f B d hfiber
  have hr : (Nat.card {ω // f ω ∈ B} : ℝ) ≤ (B.card : ℝ) * (d : ℝ) := by
    exact_mod_cast h
  simpa only [mul_comm] using hr

/-- If the sample set has at least Nd/2 elements, the endpoint probability
of a B-set is at most 2|B|/N. -/
theorem uniform_endpoint_set_bound_twice (f : Ω → V) (B : Finset V)
    (N d : ℕ) (hN : 0 < N) (hd : 0 < d)
    (hfiber : ∀ v, Nat.card {ω // f ω = v} ≤ d)
    (hsize : (N : ℝ) * (d : ℝ) / 2 ≤ (Fintype.card Ω : ℝ)) :
    eventMass (finiteUniformWeight Ω) (fun ω => f ω ∈ B) ≤
      2 * (B.card : ℝ) / (N : ℝ) := by
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hdp : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hΩp : (0 : ℝ) < Fintype.card Ω :=
    lt_of_lt_of_le (by positivity) hsize
  apply (uniform_endpoint_set_bound f B d hfiber).trans
  apply (div_le_div_iff₀ hΩp hNp).2
  have h := mul_le_mul_of_nonneg_right hsize (Nat.cast_nonneg B.card)
  nlinarith

/-- In particular each individual endpoint has probability at most 2/N. -/
theorem uniform_endpoint_vertex_bound (f : Ω → V) (v : V) (N d : ℕ)
    (hN : 0 < N) (hd : 0 < d)
    (hfiber : ∀ v, Nat.card {ω // f ω = v} ≤ d)
    (hsize : (N : ℝ) * (d : ℝ) / 2 ≤ (Fintype.card Ω : ℝ)) :
    eventMass (finiteUniformWeight Ω) (fun ω => f ω = v) ≤ 2 / (N : ℝ) := by
  have h := uniform_endpoint_set_bound_twice f {v} N d hN hd hfiber hsize
  simpa using h

/-- The finite-weight formulation agrees exactly with the standard PMF
uniform probability measure on every measurable event. -/
theorem uniform_pmf_eventMass [MeasurableSpace Ω] [Nonempty Ω]
    (P : Ω → Prop) (hP : MeasurableSet {ω | P ω}) :
    (PMF.uniformOfFintype Ω).toMeasure.real {ω | P ω} =
      eventMass (finiteUniformWeight Ω) P := by
  rw [uniform_eventMass_cardinality]
  change ((PMF.uniformOfFintype Ω).toMeasure {ω | P ω}).toReal = _
  rw [PMF.toMeasure_uniformOfFintype_apply {ω | P ω} hP]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ← Nat.card_eq_fintype_card]
  rfl

/-- The same per-vertex endpoint bound in the standard probability-measure
API used by the concentration module. -/
theorem uniform_endpoint_measure_vertex_bound [MeasurableSpace Ω] [Nonempty Ω]
    (f : Ω → V) (v : V) (N d : ℕ) (hN : 0 < N) (hd : 0 < d)
    (hfiber : ∀ v, Nat.card {ω // f ω = v} ≤ d)
    (hsize : (N : ℝ) * (d : ℝ) / 2 ≤ (Fintype.card Ω : ℝ))
    (hP : MeasurableSet {ω | f ω = v}) :
    (PMF.uniformOfFintype Ω).toMeasure.real {ω | f ω = v} ≤ 2 / (N : ℝ) := by
  rw [uniform_pmf_eventMass (fun ω => f ω = v) hP]
  exact uniform_endpoint_vertex_bound f v N d hN hd hfiber hsize

end FiniteCounting

section OutsideEdges

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The first endpoint of an actual oriented outside edge. -/
def outsideEdgeFirst (G : SimpleGraph V) (T : Set V) (e : OutsideOrientedEdge G T) : V := e.val.1

/-- The second endpoint of an actual oriented outside edge. -/
def outsideEdgeSecond (G : SimpleGraph V) (T : Set V) (e : OutsideOrientedEdge G T) : V := e.val.2

/-- Each first-endpoint fiber injects into the ambient neighbor set. -/
theorem outsideEdgeFirst_fiber_card (G : SimpleGraph V) (T : Set V) (v : V) :
    Nat.card {e : OutsideOrientedEdge G T // outsideEdgeFirst G T e = v} ≤ G.degree v := by
  let f : {e : OutsideOrientedEdge G T // outsideEdgeFirst G T e = v} → G.neighborSet v :=
    fun e => ⟨e.val.val.2, by
      have h := e.val.property.1
      have he : e.val.val.1 = v := e.property
      rw [he] at h
      exact h⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact a.property.trans b.property.symm
    · exact congrArg (fun x : G.neighborSet v => x.val) hab
  have h := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree] using h

/-- Each second-endpoint fiber has the same degree bound, by the neighbor
injection with reversed orientation. -/
theorem outsideEdgeSecond_fiber_card (G : SimpleGraph V) (T : Set V) (v : V) :
    Nat.card {e : OutsideOrientedEdge G T // outsideEdgeSecond G T e = v} ≤ G.degree v := by
  let f : {e : OutsideOrientedEdge G T // outsideEdgeSecond G T e = v} → G.neighborSet v :=
    fun e => ⟨e.val.val.1, by
      have h := e.val.property.1.symm
      have he : e.val.val.2 = v := e.property
      rw [he] at h
      exact h⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun x : G.neighborSet v => x.val) hab
    · exact a.property.trans b.property.symm
  have h := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree] using h

end OutsideEdges

namespace RegularGraph

variable {N d : ℕ}

/-- Proposition-5.9 endpoint bound for the actual sampled outside oriented
edge, once the deterministic outside-edge count has been established. -/
theorem outside_first_endpoint_probability (g : RegularGraph N d) (T : Set (Fin N))
    (hN : 0 < N) (hd : 0 < d)
    (hsize : (N : ℝ) * (d : ℝ) / 2 ≤
      (Fintype.card (OutsideOrientedEdge g.graph T) : ℝ)) (v : Fin N) :
    eventMass (finiteUniformWeight (OutsideOrientedEdge g.graph T))
      (fun e => outsideEdgeFirst g.graph T e = v) ≤ 2 / (N : ℝ) := by
  apply uniform_endpoint_vertex_bound (outsideEdgeFirst g.graph T) v N d hN hd _ hsize
  intro x
  exact (outsideEdgeFirst_fiber_card g.graph T x).trans_eq (g.regular x)

theorem outside_second_endpoint_probability (g : RegularGraph N d) (T : Set (Fin N))
    (hN : 0 < N) (hd : 0 < d)
    (hsize : (N : ℝ) * (d : ℝ) / 2 ≤
      (Fintype.card (OutsideOrientedEdge g.graph T) : ℝ)) (v : Fin N) :
    eventMass (finiteUniformWeight (OutsideOrientedEdge g.graph T))
      (fun e => outsideEdgeSecond g.graph T e = v) ≤ 2 / (N : ℝ) := by
  apply uniform_endpoint_vertex_bound (outsideEdgeSecond g.graph T) v N d hN hd _ hsize
  intro x
  exact (outsideEdgeSecond_fiber_card g.graph T x).trans_eq (g.regular x)

/-- Set-valued first-endpoint version, useful for neighborhoods in Proposition
5.10 after bounding their cardinality. -/
theorem outside_first_endpoint_set_probability (g : RegularGraph N d) (T : Set (Fin N))
    (hN : 0 < N) (hd : 0 < d)
    (hsize : (N : ℝ) * (d : ℝ) / 2 ≤
      (Fintype.card (OutsideOrientedEdge g.graph T) : ℝ)) (B : Finset (Fin N)) :
    eventMass (finiteUniformWeight (OutsideOrientedEdge g.graph T))
      (fun e => outsideEdgeFirst g.graph T e ∈ B) ≤ 2 * (B.card : ℝ) / (N : ℝ) := by
  apply uniform_endpoint_set_bound_twice (outsideEdgeFirst g.graph T) B N d hN hd _ hsize
  intro x
  exact (outsideEdgeFirst_fiber_card g.graph T x).trans_eq (g.regular x)

theorem outside_second_endpoint_set_probability (g : RegularGraph N d) (T : Set (Fin N))
    (hN : 0 < N) (hd : 0 < d)
    (hsize : (N : ℝ) * (d : ℝ) / 2 ≤
      (Fintype.card (OutsideOrientedEdge g.graph T) : ℝ)) (B : Finset (Fin N)) :
    eventMass (finiteUniformWeight (OutsideOrientedEdge g.graph T))
      (fun e => outsideEdgeSecond g.graph T e ∈ B) ≤ 2 * (B.card : ℝ) / (N : ℝ) := by
  apply uniform_endpoint_set_bound_twice (outsideEdgeSecond g.graph T) B N d hN hd _ hsize
  intro x
  exact (outsideEdgeSecond_fiber_card g.graph T x).trans_eq (g.regular x)

/-- Either endpoint can hit a specified neighborhood, with the union factor
proved explicitly. -/
theorem outside_either_endpoint_probability (g : RegularGraph N d) (T : Set (Fin N))
    (hN : 0 < N) (hd : 0 < d)
    (hsize : (N : ℝ) * (d : ℝ) / 2 ≤
      (Fintype.card (OutsideOrientedEdge g.graph T) : ℝ)) (B : Finset (Fin N)) :
    eventMass (finiteUniformWeight (OutsideOrientedEdge g.graph T))
      (fun e => outsideEdgeFirst g.graph T e ∈ B ∨ outsideEdgeSecond g.graph T e ∈ B) ≤
        4 * (B.card : ℝ) / (N : ℝ) := by
  have hunion := eventMass_union_le
    (finiteUniformWeight (OutsideOrientedEdge g.graph T)) finiteUniformWeight_nonneg
    (fun e => outsideEdgeFirst g.graph T e ∈ B)
    (fun e => outsideEdgeSecond g.graph T e ∈ B)
  have hfirst := g.outside_first_endpoint_set_probability T hN hd hsize B
  have hsecond := g.outside_second_endpoint_set_probability T hN hd hsize B
  apply hunion.trans
  calc
    _ ≤ 2 * (B.card : ℝ) / (N : ℝ) + 2 * (B.card : ℝ) / (N : ℝ) :=
      add_le_add hfirst hsecond
    _ = 4 * (B.card : ℝ) / (N : ℝ) := by ring

end RegularGraph

end LocalLaw
