import LocalLaw.CutIncidence
import LocalLaw.DeficientGraphModel

/-! # The actual missing-degree diagonal is the boundary-incidence Gram matrix -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance boundaryChargeGramDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*}

def boundaryInnerNeighborEquiv (G : SimpleGraph V) (T : Set V) (x : T) :
    {a : BoundaryOrientedEdge G T // x.val = a.val.1} ≃
      {u : (Tᶜ : Set V) // G.Adj x.val u.val} where
  toFun a := ⟨⟨a.val.val.2, a.val.property.2.2⟩, by
    have hh := a.val.property.1
    simpa only [← a.property] using hh⟩
  invFun u := ⟨⟨(x.val, u.val.val), u.property, x.property, u.val.property⟩, rfl⟩
  left_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext a.property rfl
  right_inv _ := rfl

def innerNeighborPartitionEquiv (G : SimpleGraph V) (T : Set V) (x : T) :
    G.neighborSet x.val ≃ (G.induce T).neighborSet x ⊕ {u : (Tᶜ : Set V) // G.Adj x.val u.val} where
  toFun u := if hu : u.val ∈ T then Sum.inl ⟨⟨u.val, hu⟩, u.property⟩
    else Sum.inr ⟨⟨u.val, hu⟩, u.property⟩
  invFun u := match u with
    | Sum.inl u => ⟨u.val.val, u.property⟩
    | Sum.inr u => ⟨u.val.val, u.property⟩
  left_inv u := by dsimp only; split_ifs <;> rfl
  right_inv u := by
    cases u with
    | inl u => simp only [dif_pos u.val.property]
    | inr u => simp only [dif_neg u.val.property]

namespace RegularGraph
variable {N d : ℕ}

theorem boundary_inner_fiber_degree_loss (g : RegularGraph N d) (T : Set (Fin N)) (x : T) :
    Nat.card {a : BoundaryOrientedEdge g.graph T // x.val = a.val.1} =
      d - (g.graph.induce T).degree x := by
  have hh := Nat.card_congr (innerNeighborPartitionEquiv g.graph T x)
  rw [Nat.card_sum] at hh
  simp only [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree, g.regular] at hh
  rw [Nat.card_congr (boundaryInnerNeighborEquiv g.graph T x)]
  simp only [Nat.card_eq_fintype_card]
  rw [g.regular x.val] at hh
  omega

/-- Exact normalization and all repeated boundary labels are counted. -/
theorem truncated_boundaryDiagonal_eq_cutGram (g : RegularGraph N d) (hd : 3 ≤ d) (T : Set (Fin N)) :
    (g.deficient.restrict T).boundaryDiagonal =
      cutInnerCoupling g.graph d T * (cutInnerCoupling g.graph d T).transpose := by
  let c : ℂ := ↑((Real.sqrt ((d : ℝ) - 1))⁻¹)
  have hk : 0 ≤ (d : ℝ) - 1 := by exact_mod_cast (show 0 ≤ (d : ℤ) - 1 by omega)
  have hc : c ^ 2 = (↑(((d : ℝ) - 1)⁻¹) : ℂ) := by
    dsimp only [c]
    rw [← Complex.ofReal_pow, inv_pow, Real.sq_sqrt hk]
  ext x y
  by_cases hxy : x = y
  · subst y
    have hdeg : (g.graph.induce T).degree x ≤ d :=
      (induced_degree_le g.graph T x).trans_eq (g.regular x.val)
    have hsum : (∑ a : BoundaryOrientedEdge g.graph T,
        if x.val = a.val.1 then c ^ 2 else 0) =
        (↑(d - (g.graph.induce T).degree x) : ℂ) * c ^ 2 := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      congr 1
      have hh := g.boundary_inner_fiber_degree_loss T x
      simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using congrArg (fun n : ℕ => (n : ℂ)) hh
    have hentry : (cutInnerCoupling g.graph d T * (cutInnerCoupling g.graph d T).transpose) x x =
        ∑ a : BoundaryOrientedEdge g.graph T, if x.val = a.val.1 then c ^ 2 else 0 := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, cutInnerCoupling]
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> simp only [mul_zero, sq]
      rfl
    rw [hentry, hsum, hc]
    simp only [DeficientGraph.boundaryDiagonal, Matrix.diagonal_apply_eq,
      DeficientGraph.boundaryCoefficient, DeficientGraph.restrict, deficient,
      Nat.cast_zero, sub_zero, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_natCast,
      Complex.ofReal_one, Nat.cast_sub hdeg, div_eq_mul_inv]
    push_cast
    rfl
  · have hval : x.val ≠ y.val := fun h => hxy (Subtype.ext h)
    simp only [DeficientGraph.boundaryDiagonal, Matrix.diagonal_apply, if_neg hxy]
    symm
    apply Finset.sum_eq_zero
    intro a _
    change (if x.val = a.val.1 then c else 0) * (if y.val = a.val.1 then c else 0) = 0
    by_cases hx : x.val = a.val.1
    · have hy : y.val ≠ a.val.1 := fun hy => hval (hx.trans hy.symm)
      simp only [hx, hy, if_true, if_false, mul_zero]
    · simp only [hx, if_false, zero_mul]

end RegularGraph
end LocalLaw
