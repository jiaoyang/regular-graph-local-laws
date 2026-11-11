import LocalLaw.GraphBallCounting
import LocalLaw.Resolvent

/-!
# Ward counting and actual outside-edge correlation probabilities

A large resolvent entry consumes at least phi^2 of its row's Ward mass.
The source correlation relation also permits a short graph distance and one
neighbor on either side. Its cardinality and the actual outside-edge sampling
probability are derived here. A local diagonal-imaginary-part cap is explicit;
the graph-local regularity argument supplying that cap is a separate input.
-/

open scoped BigOperators
noncomputable section

namespace LocalLaw

local instance wardCorrelationDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

section Finite

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The actual closed one-neighborhood, including its center. -/
def closedNeighborFinset (G : SimpleGraph V) (x : V) : Finset V :=
  insert x (G.neighborFinset x)

theorem closedNeighborFinset_card (G : SimpleGraph V) (x : V) :
    (closedNeighborFinset G x).card = G.degree x + 1 := by
  simp [closedNeighborFinset, SimpleGraph.card_neighborFinset_eq_degree]

theorem closedNeighborFinset_card_bound (G : SimpleGraph V) (d : ℕ)
    (hdegree : ∀ v, G.degree v ≤ d) (x : V) :
    (closedNeighborFinset G x).card ≤ d + 1 := by
  rw [closedNeighborFinset_card]
  exact Nat.add_le_add_right (hdegree x) 1

theorem mem_closedNeighborFinset_symm (G : SimpleGraph V) (x y : V) :
    y ∈ closedNeighborFinset G x ↔ x ∈ closedNeighborFinset G y := by
  simp only [closedNeighborFinset, Finset.mem_insert, SimpleGraph.mem_neighborFinset]
  rw [eq_comm, G.adj_comm]

/-- Actual large entries of a row of the Hermitian resolvent. -/
def wardLargeEntries (H : Matrix V V ℂ) (z : ℂ) (φ : ℝ) (x : V) : Finset V :=
  Finset.univ.filter (fun y => φ ≤ ‖green H z x y‖)

/-- Ward's identity gives a counting estimate, without a probability input. -/
theorem wardLargeEntries_card_bound (H : Matrix V V ℂ) (hH : H.IsHermitian)
    (z : ℂ) (hz : 0 < z.im) (φ : ℝ) (hφ : 0 < φ) (x : V) :
    ((wardLargeEntries H z φ x).card : ℝ) ≤
      (green H z x x).im / (z.im * φ ^ 2) := by
  have hsum : ((wardLargeEntries H z φ x).card : ℝ) * φ ^ 2 ≤
      ∑ y : V, ‖green H z x y‖ ^ 2 := by
    calc
      ((wardLargeEntries H z φ x).card : ℝ) * φ ^ 2 =
          ∑ _y ∈ wardLargeEntries H z φ x, φ ^ 2 := by simp
      _ ≤ ∑ y ∈ wardLargeEntries H z φ x, ‖green H z x y‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro y hy
        have hy' : φ ≤ ‖green H z x y‖ := (Finset.mem_filter.mp hy).2
        exact pow_le_pow_left₀ hφ.le hy' 2
      _ ≤ ∑ y : V, ‖green H z x y‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => sq_nonneg _)
  rw [ward_identity H hH z hz x] at hsum
  apply (le_div_iff₀ (mul_pos hz (sq_pos_of_pos hφ))).mpr
  have hmul := (le_div_iff₀ hz).mp hsum
  nlinarith

theorem wardLargeEntries_card_bound_of_im_cap (H : Matrix V V ℂ)
    (hH : H.IsHermitian) (z : ℂ) (hz : 0 < z.im) (φ : ℝ) (hφ : 0 < φ)
    (I : ℝ) (x : V) (hI : (green H z x x).im ≤ I) :
    ((wardLargeEntries H z φ x).card : ℝ) ≤ I / (z.im * φ ^ 2) :=
  (wardLargeEntries_card_bound H hH z hz φ hφ x).trans
    (div_le_div_of_nonneg_right hI (mul_pos hz (sq_pos_of_pos hφ)).le)

/-- The source relation: short distance, or a large Green entry after taking
one closed-neighborhood step from each of the two vertices. -/
def wardCorrelatedVertices (G : SimpleGraph V) (H : Matrix V V ℂ)
    (z : ℂ) (φ : ℝ) (radius : ℕ) (x : V) : Finset V :=
  (graphBallVertices G x radius).toFinset ∪
    (closedNeighborFinset G x).biUnion (fun u =>
      (wardLargeEntries H z φ u).biUnion (closedNeighborFinset G))

theorem mem_wardCorrelatedVertices (G : SimpleGraph V) (H : Matrix V V ℂ)
    (z : ℂ) (φ : ℝ) (radius : ℕ) (x y : V) :
    y ∈ wardCorrelatedVertices G H z φ radius x ↔
      G.edist x y ≤ (radius : ℕ∞) ∨
        ∃ u ∈ closedNeighborFinset G x, ∃ v ∈ closedNeighborFinset G y,
          φ ≤ ‖green H z u v‖ := by
  simp only [wardCorrelatedVertices, Finset.mem_union, Set.mem_toFinset,
    graphBallVertices, Set.mem_setOf_eq, Finset.mem_biUnion, wardLargeEntries,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (h | ⟨u, hu, v, hv, hy⟩)
    · exact Or.inl h
    · exact Or.inr ⟨u, hu, v, (mem_closedNeighborFinset_symm G v y).mp hy, hv⟩
  · rintro (h | ⟨u, hu, v, hv, hy⟩)
    · exact Or.inl h
    · exact Or.inr ⟨u, hu, v, hy, (mem_closedNeighborFinset_symm G y v).mp hv⟩

theorem wardCorrelatedVertices_card_combinatorial (G : SimpleGraph V)
    (H : Matrix V V ℂ) (z : ℂ) (φ : ℝ) (radius d : ℕ)
    (hdegree : ∀ v, G.degree v ≤ d) (x : V) :
    (wardCorrelatedVertices G H z φ radius x).card ≤
      (graphBallVertices G x radius).toFinset.card +
        ∑ u ∈ closedNeighborFinset G x, (wardLargeEntries H z φ u).card * (d + 1) := by
  apply (Finset.card_union_le _ _).trans
  apply Nat.add_le_add_left
  apply Finset.card_biUnion_le.trans
  apply Finset.sum_le_sum
  intro u _hu
  calc
    ((wardLargeEntries H z φ u).biUnion (closedNeighborFinset G)).card ≤
        ∑ v ∈ wardLargeEntries H z φ u, (closedNeighborFinset G v).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ wardLargeEntries H z φ u, (d + 1) :=
      Finset.sum_le_sum (fun v _ => closedNeighborFinset_card_bound G d hdegree v)
    _ = (wardLargeEntries H z φ u).card * (d + 1) := by simp

/-- The squared degree factor comes from the two actual closed-neighborhood
steps. The resolvent-row cap is needed only near the fixed vertex x. -/
theorem wardCorrelatedVertices_card_bound_of_near_cap (G : SimpleGraph V)
    (H : Matrix V V ℂ) (hH : H.IsHermitian) (z : ℂ) (hz : 0 < z.im)
    (φ : ℝ) (hφ : 0 < φ) (radius d : ℕ) (hdegree : ∀ v, G.degree v ≤ d)
    (I B : ℝ) (x : V)
    (hI : ∀ u ∈ closedNeighborFinset G x, (green H z u u).im ≤ I)
    (hnear : ((graphBallVertices G x radius).toFinset.card : ℝ) ≤ B) :
    ((wardCorrelatedVertices G H z φ radius x).card : ℝ) ≤
      B +
        ((d + 1 : ℕ) : ℝ) ^ 2 * I / (z.im * φ ^ 2) := by
  have hI₀ : 0 ≤ I := (green_diagonal_im_nonneg H hH z hz x).trans
    (hI x (by simp [closedNeighborFinset]))
  have hden : 0 < z.im * φ ^ 2 := mul_pos hz (sq_pos_of_pos hφ)
  have hquot : 0 ≤ I / (z.im * φ ^ 2) := div_nonneg hI₀ hden.le
  have hsum : (∑ u ∈ closedNeighborFinset G x,
      ((wardLargeEntries H z φ u).card : ℝ) * ((d + 1 : ℕ) : ℝ)) ≤
      ((d + 1 : ℕ) : ℝ) ^ 2 * I / (z.im * φ ^ 2) := by
    calc
      _ ≤ ∑ _u ∈ closedNeighborFinset G x,
          (I / (z.im * φ ^ 2)) * ((d + 1 : ℕ) : ℝ) := by
        apply Finset.sum_le_sum
        intro u hu
        exact mul_le_mul_of_nonneg_right
          (wardLargeEntries_card_bound_of_im_cap H hH z hz φ hφ I u (hI u hu))
          (Nat.cast_nonneg _)
      _ = ((closedNeighborFinset G x).card : ℝ) *
          ((I / (z.im * φ ^ 2)) * ((d + 1 : ℕ) : ℝ)) := by simp
      _ ≤ ((d + 1 : ℕ) : ℝ) *
          ((I / (z.im * φ ^ 2)) * ((d + 1 : ℕ) : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg hquot (Nat.cast_nonneg _))
        exact_mod_cast closedNeighborFinset_card_bound G d hdegree x
      _ = ((d + 1 : ℕ) : ℝ) ^ 2 * I / (z.im * φ ^ 2) := by ring
  have hcomb := wardCorrelatedVertices_card_combinatorial G H z φ radius d hdegree x
  have hcomb' : ((wardCorrelatedVertices G H z φ radius x).card : ℝ) ≤
      ((graphBallVertices G x radius).toFinset.card : ℝ) +
        ∑ u ∈ closedNeighborFinset G x,
          ((wardLargeEntries H z φ u).card : ℝ) * ((d + 1 : ℕ) : ℝ) := by
    exact_mod_cast hcomb
  exact hcomb'.trans (add_le_add hnear hsum)

/-- Coarse radius specialization, using the actual finite graph-ball bound. -/
theorem wardCorrelatedVertices_card_bound (G : SimpleGraph V)
    (H : Matrix V V ℂ) (hH : H.IsHermitian) (z : ℂ) (hz : 0 < z.im)
    (φ : ℝ) (hφ : 0 < φ) (radius d : ℕ) (hdegree : ∀ v, G.degree v ≤ d)
    (I : ℝ) (x : V)
    (hI : ∀ u ∈ closedNeighborFinset G x, (green H z u u).im ≤ I) :
    ((wardCorrelatedVertices G H z φ radius x).card : ℝ) ≤
      ((d + 1 : ℕ) : ℝ) ^ radius +
        ((d + 1 : ℕ) : ℝ) ^ 2 * I / (z.im * φ ^ 2) := by
  apply wardCorrelatedVertices_card_bound_of_near_cap G H hH z hz φ hφ radius d hdegree
    I (((d + 1 : ℕ) : ℝ) ^ radius) x hI
  have h := graphBall_card_bound G x d hdegree radius
  rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
  exact_mod_cast h

end Finite

namespace RegularGraph

variable {N d : ℕ}

/-- Actual correlated vertices of the deleted graph G(T), kept as ambient
vertices solely to apply the already-proved outside-edge endpoint law. -/
def outsideCorrelatedVertices (g : RegularGraph N d) (T : Set (Fin N))
    (z : ℂ) (φ : ℝ) (radius : ℕ) (x : {v : Fin N // v ∉ T}) : Finset (Fin N) :=
  (wardCorrelatedVertices (outsideGraph g.graph T)
    (normalizedAdjacency (outsideGraph g.graph T) d) z φ radius x).image Subtype.val

/-- The correlation-event probability (the mechanism of (5.15)) follows from
Ward, graph-neighborhood counting and the actual outside-edge sampling law.
No correlation-probability estimate is assumed. -/
theorem outside_correlated_endpoint_probability (g : RegularGraph N d)
    (T : Set (Fin N)) (hN : 0 < N) (hd : 0 < d) (hT : 4 * Nat.card T ≤ N)
    (z : ℂ) (hz : 0 < z.im) (φ : ℝ) (hφ : 0 < φ) (radius : ℕ) (I : ℝ)
    (x : {v : Fin N // v ∉ T})
    (hI : ∀ u ∈ closedNeighborFinset (outsideGraph g.graph T) x,
      (green (normalizedAdjacency (outsideGraph g.graph T) d) z u u).im ≤ I) :
    eventMass (finiteUniformWeight (OutsideOrientedEdge g.graph T))
      (fun e => outsideEdgeFirst g.graph T e ∈ outsideCorrelatedVertices g T z φ radius x ∨
        outsideEdgeSecond g.graph T e ∈ outsideCorrelatedVertices g T z φ radius x) ≤
      4 / (N : ℝ) * (((d + 1 : ℕ) : ℝ) ^ radius +
        ((d + 1 : ℕ) : ℝ) ^ 2 * I / (z.im * φ ^ 2)) := by
  have hdegree : ∀ v, (outsideGraph g.graph T).degree v ≤ d := by
    intro v
    have hv := (induced_degree_le g.graph {v | v ∉ T} v).trans (g.regular v.val).le
    simpa only [outsideGraph, SimpleGraph.degree, SimpleGraph.neighborFinset,
      Set.toFinset_card, ← Nat.card_eq_fintype_card] using hv
  have hcard := wardCorrelatedVertices_card_bound (outsideGraph g.graph T)
    (normalizedAdjacency (outsideGraph g.graph T) d)
    (normalizedAdjacency_isHermitian _ _) z hz φ hφ radius d hdegree I x hI
  have himage : (outsideCorrelatedVertices g T z φ radius x).card =
      (wardCorrelatedVertices (outsideGraph g.graph T)
        (normalizedAdjacency (outsideGraph g.graph T) d) z φ radius x).card := by
    exact Finset.card_image_of_injective _ Subtype.val_injective
  have hprob := g.outside_either_endpoint_probability T hN hd
    (g.outside_edge_real_size T hT) (outsideCorrelatedVertices g T z φ radius x)
  apply hprob.trans
  rw [himage, show 4 * ((wardCorrelatedVertices (outsideGraph g.graph T)
    (normalizedAdjacency (outsideGraph g.graph T) d) z φ radius x).card : ℝ) / (N : ℝ) =
    (4 / (N : ℝ)) * ((wardCorrelatedVertices (outsideGraph g.graph T)
      (normalizedAdjacency (outsideGraph g.graph T) d) z φ radius x).card : ℝ) by ring]
  exact mul_le_mul_of_nonneg_left hcard (div_nonneg (by norm_num) (Nat.cast_nonneg _))

end RegularGraph

end LocalLaw
