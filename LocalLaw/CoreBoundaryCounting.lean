import LocalLaw.CoreAttachments

/-!
# Exact finite boundary counting for core aggregation

These identities partition actual vertices by the core and its components,
and actual cut edges by their core endpoint. No port-count or summation
identity is supplied as a hypothesis.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw

local instance coreBoundaryCountDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*} [Fintype V]

theorem sum_core_components (G : SimpleGraph V) (C : Set V) (f : V → ℝ) :
    (∑ v : V, f v) = (∑ v : C, f v.val) +
      ∑ A : CutComponent G C, ∑ v : A.supp, f v.val.val := by
  have hsplit := Fintype.sum_subtype_add_sum_subtype (fun v : V => v ∈ C) f
  have hout : (∑ p : (Σ A : CutComponent G C, A.supp), f p.2.val.val) =
      ∑ v : {v : V // v ∉ C}, f v.val := by
    apply Fintype.sum_equiv (componentVertexEquiv (outsideGraph G C))
    intro p
    rfl
  rw [Fintype.sum_sigma] at hout
  simp only [← finsum_eq_sum_of_fintype] at hsplit hout ⊢
  rw [← hout] at hsplit
  exact hsplit.symm

/-- Actual outside neighbors of a core vertex. -/
def outsideCoreNeighborCount (G : SimpleGraph V) (C : Set V) (u : C) : ℕ :=
  Nat.card {v : V // v ∉ C ∧ G.Adj u.val v}

def neighborCorePartitionEquiv (G : SimpleGraph V) (C : Set V) (u : C) :
    G.neighborSet u.val ≃ (G.induce C).neighborSet u ⊕ {v : V // v ∉ C ∧ G.Adj u.val v} where
  toFun y := if hy : y.val ∈ C then Sum.inl ⟨⟨y.val, hy⟩, y.property⟩
    else Sum.inr ⟨y.val, hy, y.property⟩
  invFun
    | Sum.inl y => ⟨y.val.val, y.property⟩
    | Sum.inr y => ⟨y.val, y.property.2⟩
  left_inv y := by by_cases hy : y.val ∈ C <;> simp [hy]
  right_inv y := by
    rcases y with y | y
    · simp [y.val.property]
    · simp [y.property.1]

theorem core_neighbor_degree_partition (G : SimpleGraph V) (C : Set V) (u : C) :
    G.degree u.val = (G.induce C).degree u + outsideCoreNeighborCount G C u := by
  have h := Nat.card_congr (neighborCorePartitionEquiv G C u)
  rw [Nat.card_sum] at h
  simp only [outsideCoreNeighborCount, ← SimpleGraph.card_neighborSet_eq_degree,
    ← Nat.card_eq_fintype_card]
  exact h

def boundaryFirstVertexEquiv (G : SimpleGraph V) (C : Set V) :
    BoundaryOrientedEdge G C ≃ Σ u : C, {v : V // v ∉ C ∧ G.Adj u.val v} where
  toFun e := ⟨⟨e.val.1, e.property.2.1⟩, ⟨e.val.2, e.property.2.2, e.property.1⟩⟩
  invFun p := ⟨(p.1.val, p.2.val), p.2.property.2, p.1.property, p.2.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The exact port-weighted edge count, without a uniform-endpoint premise. -/
theorem sum_boundary_ports (G : SimpleGraph V) (C : Set V) (f : V → ℝ) :
    (∑ e : BoundaryOrientedEdge G C, f e.val.1) =
      ∑ u : C, (outsideCoreNeighborCount G C u : ℝ) * f u.val := by
  have hsum : (∑ e : BoundaryOrientedEdge G C, f e.val.1) =
      ∑ p : (Σ u : C, {v : V // v ∉ C ∧ G.Adj u.val v}), f p.1.val := by
    apply Fintype.sum_equiv (boundaryFirstVertexEquiv G C)
    intro e
    rfl
  rw [Fintype.sum_sigma] at hsum
  simpa only [outsideCoreNeighborCount, Nat.card_eq_fintype_card, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul] using hsum

/-- Choosing the unique actual edge for each singly attached component
enumerates the whole actual cut boundary exactly once. -/
theorem sum_unique_cut_ports (G : SimpleGraph V) (C : Set V)
    (hcount : ∀ A : CutComponent G C, cutMultiplicity G C A = 1)
    (pick : ∀ A : CutComponent G C, CutBoundaryEdge G C A) (f : V → ℝ) :
    (∑ A : CutComponent G C, f (pick A).val.val.1) =
      ∑ u : C, (outsideCoreNeighborCount G C u : ℝ) * f u.val := by
  have hper : ∀ A : CutComponent G C,
      (∑ e : CutBoundaryEdge G C A, f e.val.val.1) = f (pick A).val.val.1 := by
    intro A
    letI : Unique (CutBoundaryEdge G C A) :=
      { default := pick A
        uniq := fun e => (Nat.card_eq_one_iff_unique.mp (hcount A)).1.elim e (pick A) }
    exact Fintype.sum_unique _
  have hboundary : (∑ p : (Σ A : CutComponent G C, CutBoundaryEdge G C A), f p.2.val.val.1) =
      ∑ e : BoundaryOrientedEdge G C, f e.val.1 := by
    apply Fintype.sum_equiv (cutBoundaryEquiv G C).symm
    intro p
    rfl
  rw [Fintype.sum_sigma] at hboundary
  have hfirst : (∑ A : CutComponent G C, f (pick A).val.val.1) =
      ∑ e : BoundaryOrientedEdge G C, f e.val.1 := by
    rw [← hboundary]
    exact Finset.sum_congr rfl (fun A _ => (hper A).symm)
  exact hfirst.trans (sum_boundary_ports G C f)

/-- Exact component and port enumeration turns proved component estimates
and local degree coefficients into a core sum. -/
theorem boundary_sum_reduction (G : SimpleGraph V) (C : Set V)
    (hcount : ∀ A : CutComponent G C, cutMultiplicity G C A = 1)
    (pick : ∀ A : CutComponent G C, CutBoundaryEdge G C A)
    (w f : V → ℝ) (q K : ℝ)
    (branches : ∀ A : CutComponent G C, (∑ᶠ v : A.supp, w v.val.val * f v.val.val) ≤
      q * f (pick A).val.val.1)
    (coefficients : ∀ u : C, w u.val + (outsideCoreNeighborCount G C u : ℝ) * q ≤ K)
    (hf : ∀ u : C, 0 ≤ f u.val) :
    (∑ v : V, w v * f v) ≤ K * ∑ u : C, f u.val := by
  have hsplit := sum_core_components G C (fun v => w v * f v)
  have hports := sum_unique_cut_ports G C hcount pick (fun v => q * f v)
  calc
    _ = (∑ u : C, w u.val * f u.val) +
        ∑ A : CutComponent G C, ∑ v : A.supp, w v.val.val * f v.val.val := hsplit
    _ ≤ (∑ u : C, w u.val * f u.val) +
        ∑ A : CutComponent G C, q * f (pick A).val.val.1 :=
      add_le_add_left (Finset.sum_le_sum (fun A _ => by
        simpa only [← finsum_eq_sum_of_fintype] using branches A)) _
    _ = (∑ u : C, w u.val * f u.val) +
        ∑ u : C, (outsideCoreNeighborCount G C u : ℝ) * (q * f u.val) := by rw [hports]
    _ = ∑ u : C, (w u.val + (outsideCoreNeighborCount G C u : ℝ) * q) * f u.val := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro u _
      ring
    _ ≤ ∑ u : C, K * f u.val := Finset.sum_le_sum (fun u _ =>
      mul_le_mul_of_nonneg_right (coefficients u) (hf u))
    _ = K * ∑ u : C, f u.val := by rw [Finset.mul_sum]

end LocalLaw
