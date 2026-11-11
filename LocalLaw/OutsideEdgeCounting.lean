import LocalLaw.EndpointSampling

/-!
# Exact counts of oriented edges outside a removed vertex set

Finite equivalences partition the actual oriented edges. For a d-regular graph,
O+2B+I=Nd and B+I=d|T|, hence O>=Nd-2d|T|. In particular |T|<=N/4 proves the
sample-size hypothesis used by EndpointSampling, rather than assuming it.
-/

open scoped BigOperators
noncomputable section

namespace LocalLaw

local instance outsideCountingDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Both endpoints are inside T. -/
def InteriorOrientedEdge {V : Type*} (G : SimpleGraph V) (T : Set V) :=
  {e : V × V // G.Adj e.1 e.2 ∧ e.1 ∈ T ∧ e.2 ∈ T}

instance interiorOrientedEdgeFintype {V : Type*} [Fintype V] (G : SimpleGraph V) (T : Set V) :
    Fintype (InteriorOrientedEdge G T) := by
  unfold InteriorOrientedEdge
  infer_instance

/-- The first endpoint is in T, with no restriction on the second endpoint. -/
def FirstInsideOrientedEdge {V : Type*} (G : SimpleGraph V) (T : Set V) :=
  {e : V × V // G.Adj e.1 e.2 ∧ e.1 ∈ T}

instance firstInsideOrientedEdgeFintype {V : Type*} [Fintype V] (G : SimpleGraph V) (T : Set V) :
    Fintype (FirstInsideOrientedEdge G T) := by
  unfold FirstInsideOrientedEdge
  infer_instance

/-- Four endpoint-membership cases, with entering boundary edges reversed
into the same boundary-edge type used by local resampling. -/
def dart_partition_equiv {V : Type*} (G : SimpleGraph V) (T : Set V) :
    G.Dart ≃ OutsideOrientedEdge G T ⊕
      (BoundaryOrientedEdge G T ⊕ (BoundaryOrientedEdge G T ⊕ InteriorOrientedEdge G T)) where
  toFun e := if ha : e.fst ∈ T then
      if hb : e.snd ∈ T then Sum.inr (Sum.inr (Sum.inr ⟨e.toProd, e.adj, ha, hb⟩))
      else Sum.inr (Sum.inl ⟨e.toProd, e.adj, ha, hb⟩)
    else if hb : e.snd ∈ T then Sum.inr (Sum.inr (Sum.inl ⟨(e.snd, e.fst), e.adj.symm, hb, ha⟩))
      else Sum.inl ⟨e.toProd, e.adj, ha, hb⟩
  invFun
    | Sum.inl e => ⟨e.val, e.property.1⟩
    | Sum.inr (Sum.inl e) => ⟨e.val, e.property.1⟩
    | Sum.inr (Sum.inr (Sum.inl e)) => ⟨(e.val.2, e.val.1), e.property.1.symm⟩
    | Sum.inr (Sum.inr (Sum.inr e)) => ⟨e.val, e.property.1⟩
  left_inv e := by
    by_cases ha : e.fst ∈ T <;> by_cases hb : e.snd ∈ T <;>
      simp only [ha, hb, dif_pos, dif_neg] <;> apply SimpleGraph.Dart.ext <;> rfl
  right_inv x := by
    rcases x with e | e | e | e
    · simp [e.property.2.1, e.property.2.2]
    · simp [e.property.2.1, e.property.2.2]
    · simp [e.property.2.1, e.property.2.2]
    · simp [e.property.2.1, e.property.2.2]

/-- Splitting the second endpoint of a first-inside edge gives boundary or
interior edges. -/
def firstInside_partition_equiv {V : Type*} (G : SimpleGraph V) (T : Set V) :
    FirstInsideOrientedEdge G T ≃ BoundaryOrientedEdge G T ⊕ InteriorOrientedEdge G T where
  toFun e := if hb : e.val.2 ∈ T then Sum.inr ⟨e.val, e.property.1, e.property.2, hb⟩
    else Sum.inl ⟨e.val, e.property.1, e.property.2, hb⟩
  invFun
    | Sum.inl e => ⟨e.val, e.property.1, e.property.2.1⟩
    | Sum.inr e => ⟨e.val, e.property.1, e.property.2.1⟩
  left_inv e := by
    by_cases h : e.val.2 ∈ T <;> simp [h]
  right_inv e := by
    rcases e with e | e
    · simp [e.property.2.2]
    · simp [e.property.2.2]

/-- Count first-inside edges by choosing an inside vertex and then a neighbor. -/
def firstInside_neighbor_equiv {V : Type*} (G : SimpleGraph V) (T : Set V) :
    FirstInsideOrientedEdge G T ≃ Σ v : T, G.neighborSet v.val where
  toFun e := ⟨⟨e.val.1, e.property.2⟩, ⟨e.val.2, e.property.1⟩⟩
  invFun p := ⟨(p.1.val, p.2.val), p.2.property, p.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Interior oriented edges are exactly darts of the actual induced graph. -/
def interior_induced_dart_equiv {V : Type*} (G : SimpleGraph V) (T : Set V) :
    InteriorOrientedEdge G T ≃ (G.induce T).Dart where
  toFun e := ⟨(⟨e.val.1, e.property.2.1⟩, ⟨e.val.2, e.property.2.2⟩), e.property.1⟩
  invFun e := ⟨(e.fst.val, e.snd.val), e.adj, e.fst.property, e.snd.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

section Counts

variable {V : Type*} [Fintype V]

/-- Exact finite partition of all oriented edges. -/
theorem outside_boundary_interior_count (G : SimpleGraph V) (T : Set V) :
    Nat.card G.Dart = Nat.card (OutsideOrientedEdge G T) +
      2 * Nat.card (BoundaryOrientedEdge G T) + Nat.card (InteriorOrientedEdge G T) := by
  have h := Nat.card_congr (dart_partition_equiv G T)
  simp only [Nat.card_sum] at h
  omega

/-- First-inside edges split into boundary and interior edges. -/
theorem firstInside_count (G : SimpleGraph V) (T : Set V) :
    Nat.card (FirstInsideOrientedEdge G T) = Nat.card (BoundaryOrientedEdge G T) +
      Nat.card (InteriorOrientedEdge G T) := by
  have h := Nat.card_congr (firstInside_partition_equiv G T)
  simpa only [Nat.card_sum] using h

/- Only the induced graph on T determines the count of interior oriented
edges, independent of the graph outside T. -/
omit [Fintype V] in
theorem interior_count_induced (G : SimpleGraph V) (T : Set V) :
    Nat.card (InteriorOrientedEdge G T) = Nat.card (G.induce T).Dart :=
  Nat.card_congr (interior_induced_dart_equiv G T)

end Counts

namespace RegularGraph

variable {N d : ℕ}

/-- A regular graph has exactly Nd oriented edges. -/
theorem oriented_edge_count (g : RegularGraph N d) : Nat.card g.graph.Dart = N * d := by
  rw [Nat.card_eq_fintype_card, g.graph.dart_card_eq_twice_card_edges]
  exact g.degree_sum.symm

/-- Exact root-side degree count; no asymptotic neighborhood bound is used. -/
theorem firstInside_edge_count (g : RegularGraph N d) (T : Set (Fin N)) :
    Nat.card (FirstInsideOrientedEdge g.graph T) = d * Nat.card T := by
  rw [Nat.card_congr (firstInside_neighbor_equiv g.graph T), Nat.card_sigma]
  have hdegree : ∀ v : T, Nat.card (g.graph.neighborSet v.val) = d := by
    intro v
    rw [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree, g.regular v.val]
  simp only [hdegree, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card]
  simp [mul_comm]

/-- The exact boundary-plus-interior identity for a regular graph. -/
theorem boundary_interior_count (g : RegularGraph N d) (T : Set (Fin N)) :
    Nat.card (BoundaryOrientedEdge g.graph T) + Nat.card (InteriorOrientedEdge g.graph T) =
      d * Nat.card T := by
  rw [← firstInside_count, g.firstInside_edge_count]

/-- The exact outside-plus-two-boundaries-plus-interior identity. -/
theorem outside_count_identity (g : RegularGraph N d) (T : Set (Fin N)) :
    Nat.card (OutsideOrientedEdge g.graph T) + 2 * Nat.card (BoundaryOrientedEdge g.graph T) +
      Nat.card (InteriorOrientedEdge g.graph T) = N * d := by
  rw [← outside_boundary_interior_count, g.oriented_edge_count]

/-- A lower bound obtained by deleting at most the two endpoint-incidence
counts. The natural subtraction occurs after forming the full count. -/
theorem outside_edge_count_lower (g : RegularGraph N d) (T : Set (Fin N)) :
    N * d - 2 * d * Nat.card T ≤ Nat.card (OutsideOrientedEdge g.graph T) := by
  have h₁ := g.outside_count_identity T
  have h₂ := g.boundary_interior_count T
  apply Nat.sub_le_iff_le_add.mpr
  nlinarith

/-- Removing at most N/4 vertices leaves at least half of all oriented edges. -/
theorem outside_edge_count_half (g : RegularGraph N d) (T : Set (Fin N))
    (hT : 4 * Nat.card T ≤ N) :
    N * d ≤ 2 * Nat.card (OutsideOrientedEdge g.graph T) := by
  have h₁ := g.outside_count_identity T
  have h₂ := g.boundary_interior_count T
  have hprod := Nat.mul_le_mul_right d hT
  nlinarith

/-- The real sample-size hypothesis in Proposition 5.9 is now discharged. -/
theorem outside_edge_real_size (g : RegularGraph N d) (T : Set (Fin N))
    (hT : 4 * Nat.card T ≤ N) :
    (N : ℝ) * (d : ℝ) / 2 ≤ (Fintype.card (OutsideOrientedEdge g.graph T) : ℝ) := by
  have h := g.outside_edge_count_half T hT
  rw [Nat.card_eq_fintype_card] at h
  have hr : (N : ℝ) * (d : ℝ) ≤ 2 * (Fintype.card (OutsideOrientedEdge g.graph T) : ℝ) := by
    exact_mod_cast h
  linarith

/-- Positive N,d and the deterministic deletion-size condition prove that
there actually is an outside oriented edge to sample. -/
theorem outside_edge_nonempty (g : RegularGraph N d) (T : Set (Fin N))
    (hN : 0 < N) (hd : 0 < d) (hT : 4 * Nat.card T ≤ N) :
    Nonempty (OutsideOrientedEdge g.graph T) := by
  have h := g.outside_edge_count_half T hT
  have hpos : 0 < Nat.card (OutsideOrientedEdge g.graph T) := by
    nlinarith [Nat.mul_pos hN hd]
  exact (Nat.card_pos_iff.mp hpos).1

/-- The unconditional counting form of Proposition 5.9 for any small removed
vertex set: no endpoint probability or outside-edge count is assumed. -/
theorem outside_endpoint_probability_of_small_set (g : RegularGraph N d)
    (T : Set (Fin N)) (hN : 0 < N) (hd : 0 < d) (hT : 4 * Nat.card T ≤ N) (v : Fin N) :
    eventMass (finiteUniformWeight (OutsideOrientedEdge g.graph T))
      (fun e => outsideEdgeFirst g.graph T e = v) ≤ 2 / (N : ℝ) ∧
    eventMass (finiteUniformWeight (OutsideOrientedEdge g.graph T))
      (fun e => outsideEdgeSecond g.graph T e = v) ≤ 2 / (N : ℝ) := by
  exact ⟨g.outside_first_endpoint_probability T hN hd (g.outside_edge_real_size T hT) v,
    g.outside_second_endpoint_probability T hN hd (g.outside_edge_real_size T hT) v⟩

/-- Preserving the induced graph on T preserves both boundary and outside
sample counts, which is the counting input to measure preservation. -/
theorem boundary_outside_count_invariant (g h : RegularGraph N d) (T : Set (Fin N))
    (hinduced : g.graph.induce T = h.graph.induce T) :
    Nat.card (BoundaryOrientedEdge g.graph T) = Nat.card (BoundaryOrientedEdge h.graph T) ∧
    Nat.card (OutsideOrientedEdge g.graph T) = Nat.card (OutsideOrientedEdge h.graph T) := by
  have hI : Nat.card (InteriorOrientedEdge g.graph T) = Nat.card (InteriorOrientedEdge h.graph T) := by
    rw [interior_count_induced, interior_count_induced, hinduced]
  have hg₁ := g.boundary_interior_count T
  have hh₁ := h.boundary_interior_count T
  have hg₂ := g.outside_count_identity T
  have hh₂ := h.outside_count_identity T
  omega

/-- The actual dependent sample-fiber cardinality is constant on an induced
T-neighborhood block, as required by Proposition 3.5's counting argument. -/
theorem local_sampling_fiber_count_invariant (g h : RegularGraph N d) (T : Set (Fin N))
    (hinduced : g.graph.induce T = h.graph.induce T) :
    Nat.card (LocalSamplingFiber g.graph T) = Nat.card (LocalSamplingFiber h.graph T) := by
  have hcounts := g.boundary_outside_count_invariant h T hinduced
  simp only [LocalSamplingFiber, Nat.card_fun, hcounts.1, hcounts.2]

/-- Fintype-cardinality version ready for the invariant-block preservation
lemma in FiniteResampling. -/
theorem local_sampling_fiber_card_invariant (g h : RegularGraph N d) (T : Set (Fin N))
    (hinduced : g.graph.induce T = h.graph.induce T) :
    Fintype.card (LocalSamplingFiber g.graph T) = Fintype.card (LocalSamplingFiber h.graph T) := by
  simp only [← Nat.card_eq_fintype_card]
  exact g.local_sampling_fiber_count_invariant h T hinduced

/-- The actual local sampling fiber is nonempty under the deterministic size
condition, completing the prerequisites for uniform dependent sampling. -/
theorem local_sampling_fiber_nonempty_of_small_set (g : RegularGraph N d) (T : Set (Fin N))
    (hN : 0 < N) (hd : 0 < d) (hT : 4 * Nat.card T ≤ N) :
    Nonempty (LocalSamplingFiber g.graph T) :=
  localSamplingFiber_nonempty g.graph T (g.outside_edge_nonempty T hN hd hT)

end RegularGraph

end LocalLaw
