import LocalLaw.GraphExcessSurgery

/-!
# Actual cut parity for even edge patterns

The sum of ambient degrees in an outside component is twice its internal
edge count plus its actual attachment multiplicity. Hence an even-degree
edge pattern crosses every such component cut an even number of times.
In particular a nonempty crossing cannot use just one boundary edge. This
is the cut argument needed to keep short cycles out of isolated resampling
tree gadgets.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 800000
namespace LocalLaw

local instance evenCutsetsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*} [Fintype V]

theorem cutComponent_ambient_degree_identity (G : SimpleGraph V) (T : Set V)
    (C : CutComponent G T) (v : C.supp) :
    G.degree v.val.val = (cutComponentGraph G T C).degree v + cutDeficit G T C v := by
  have hle₁ := induced_degree_le (outsideGraph G T) C.supp v
  have hle₂ := induced_degree_le G {w | w ∉ T} v.val
  have hdef := cutDeficit_degree_loss G T C v
  simp only [cutComponentGraph, outsideGraph, ← SimpleGraph.card_neighborSet_eq_degree,
    ← Nat.card_eq_fintype_card] at hle₁ hle₂ hdef ⊢
  omega

/-- Exact handshake count for an actual outside connected component. -/
theorem cutComponent_ambient_degree_sum (G : SimpleGraph V) (T : Set V)
    (C : CutComponent G T) :
    (∑ v : C.supp, G.degree v.val.val) =
      2 * graphEdgeCount (cutComponentGraph G T C) + cutMultiplicity G T C := by
  have hpoint : (∑ v : C.supp, G.degree v.val.val) =
      (∑ v : C.supp, ((cutComponentGraph G T C).degree v + cutDeficit G T C v)) :=
    Finset.sum_congr rfl (fun v _ => cutComponent_ambient_degree_identity G T C v)
  rw [Finset.sum_add_distrib] at hpoint
  have hhand := (cutComponentGraph G T C).sum_degrees_eq_twice_card_edges
  have hcut := cutMultiplicity_eq_sum_deficit G T C
  simp only [graphEdgeCount, SimpleGraph.edgeFinset_card,
    ← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card,
    ← finsum_eq_sum_of_fintype] at hpoint hhand hcut ⊢
  omega

/-- Every actual outside-component cut of an even-degree graph has even
attachment multiplicity. The claim is derived from degrees, not assumed. -/
theorem cutMultiplicity_even (G : SimpleGraph V) (T : Set V)
    (heven : ∀ v, Even (G.degree v)) (C : CutComponent G T) :
    Even (cutMultiplicity G T C) := by
  have hsum : Even (∑ v : C.supp, G.degree v.val.val) := by
    have hfinite : ∀ s : Finset C.supp, Even (∑ v ∈ s, G.degree v.val.val) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert v s hv ih =>
          rw [Finset.sum_insert hv]
          exact (heven v.val.val).add ih
    exact hfinite Finset.univ
  rw [cutComponent_ambient_degree_sum G T C] at hsum
  exact (Nat.even_add.mp hsum).mp (even_two_mul _)

theorem cutMultiplicity_eq_zero_of_even_le_one (G : SimpleGraph V) (T : Set V)
    (heven : ∀ v, Even (G.degree v)) (C : CutComponent G T)
    (hbound : cutMultiplicity G T C ≤ 1) : cutMultiplicity G T C = 0 := by
  obtain ⟨k, hk⟩ := cutMultiplicity_even G T heven C
  omega

theorem cutMultiplicity_two_le_of_even_positive (G : SimpleGraph V) (T : Set V)
    (heven : ∀ v, Even (G.degree v)) (C : CutComponent G T)
    (hpositive : 0 < cutMultiplicity G T C) : 2 ≤ cutMultiplicity G T C := by
  obtain ⟨k, hk⟩ := cutMultiplicity_even G T heven C
  omega

end LocalLaw
