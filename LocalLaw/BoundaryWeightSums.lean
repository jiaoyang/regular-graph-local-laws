import LocalLaw.KernelSquareSum
import LocalLaw.GraphConcentration

/-!
# Boundary incidence and product-weight budgets

Actual boundary labels repeat an inner vertex at most its degree many times.
The L1, squared-L2 and maximum product-weight estimates follow from the
genuine finite Green row sums and root-to-boundary decay. No weight bound is
assumed in place of these finite incidence and norm inequalities.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance boundaryWeightSumsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem finite_fiber_nonnegative_sum_bound {I V : Type*} [Fintype I] [Fintype V]
    (l : I → V) (d : ℕ) (hfiber : ∀ v, Nat.card {i : I // l i = v} ≤ d)
    (f : V → ℝ) (hf : ∀ v, 0 ≤ f v) : (∑ i, f (l i)) ≤ (d : ℝ) * ∑ v, f v := by
  have hmaps : ∀ i ∈ (Finset.univ : Finset I), l i ∈ (Finset.univ : Finset V) := fun i _ => Finset.mem_univ (l i)
  have hsplit := (Finset.sum_fiberwise_of_maps_to hmaps (fun i => f (l i))).symm
  have hper (v : V) : (∑ i ∈ Finset.univ.filter (fun i => l i = v), f (l i)) ≤ (d : ℝ) * f v := by
    have hc : (Finset.univ.filter (fun i => l i = v)).card ≤ d := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using hfiber v
    calc
      _ = ∑ _i ∈ Finset.univ.filter (fun i => l i = v), f v :=
        Finset.sum_congr rfl (fun i hi => congrArg f (Finset.mem_filter.mp hi).2)
      _ = ((Finset.univ.filter (fun i => l i = v)).card : ℝ) * f v := by simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hc) (hf v)
  calc
    _ = ∑ v, ∑ i ∈ Finset.univ.filter (fun i => l i = v), f (l i) := hsplit
    _ ≤ ∑ v, (d : ℝ) * f v := Finset.sum_le_sum (fun v _ => hper v)
    _ = _ := (Finset.mul_sum ..).symm

theorem boundary_inner_fiber_card {V : Type*} [Fintype V]
    (G : SimpleGraph V) (T : Set V) (v : V) :
    Nat.card {e : BoundaryOrientedEdge G T // e.val.1 = v} ≤ G.degree v := by
  let F : {e : BoundaryOrientedEdge G T // e.val.1 = v} → G.neighborSet v := fun e =>
    ⟨e.val.val.2, by simpa only [e.property] using e.val.property.1⟩
  have hF : Function.Injective F := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact x.property.trans y.property.symm
    · exact congrArg (fun w : G.neighborSet v => w.val) h
  have hh := Nat.card_le_card_of_injective F hF
  simpa only [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree] using hh

theorem product_weight_l1_bound {I V : Type*} [Fintype I] [Fintype V]
    (l : I → V) (d : ℕ) (hfiber : ∀ v, Nat.card {i : I // l i = v} ≤ d)
    (K : Matrix V V ℂ) (o i : V) (S : ℝ)
    (hroot : (∑ v, ‖K o v‖ ^ 2) ≤ S) (hrow : (∑ v, ‖K i v‖ ^ 2) ≤ S) :
    (∑ a, ‖K o (l a) * K i (l a)‖) ≤ (d : ℝ) * S := by
  have hroot' := finite_fiber_nonnegative_sum_bound l d hfiber (fun v => ‖K o v‖ ^ 2) (fun _ => sq_nonneg _)
  have hrow' := finite_fiber_nonnegative_sum_bound l d hfiber (fun v => ‖K i v‖ ^ 2) (fun _ => sq_nonneg _)
  have hh : (∑ a, ‖K o (l a) * K i (l a)‖) ≤
      ((∑ a, ‖K o (l a)‖ ^ 2) + (∑ a, ‖K i (l a)‖ ^ 2)) / 2 := by
    calc
      _ ≤ ∑ a, (‖K o (l a)‖ ^ 2 + ‖K i (l a)‖ ^ 2) / 2 := by
        apply Finset.sum_le_sum
        intro a _
        rw [norm_mul]
        nlinarith [sq_nonneg (‖K o (l a)‖ - ‖K i (l a)‖)]
      _ = _ := by rw [← Finset.sum_div, Finset.sum_add_distrib]
  have ho := hroot'.trans (mul_le_mul_of_nonneg_left hroot (Nat.cast_nonneg d))
  have hi := hrow'.trans (mul_le_mul_of_nonneg_left hrow (Nat.cast_nonneg d))
  linarith

theorem product_weight_l2_bound {I V : Type*} [Fintype I] [Fintype V]
    (l : I → V) (d : ℕ) (hfiber : ∀ v, Nat.card {i : I // l i = v} ≤ d)
    (K : Matrix V V ℂ) (o i : V) (M S : ℝ) (_hM : 0 ≤ M)
    (hroot : ∀ a, ‖K o (l a)‖ ≤ M) (hrow : (∑ v, ‖K i v‖ ^ 2) ≤ S) :
    (∑ a, ‖K o (l a) * K i (l a)‖ ^ 2) ≤ M ^ 2 * ((d : ℝ) * S) := by
  have hi := (finite_fiber_nonnegative_sum_bound l d hfiber (fun v => ‖K i v‖ ^ 2)
    (fun _ => sq_nonneg _)).trans (mul_le_mul_of_nonneg_left hrow (Nat.cast_nonneg d))
  calc
    _ ≤ ∑ a, M ^ 2 * ‖K i (l a)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro a _
      rw [norm_mul, mul_pow]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hroot a) 2) (sq_nonneg _)
    _ = M ^ 2 * ∑ a, ‖K i (l a)‖ ^ 2 := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hi (sq_nonneg M)

theorem product_weight_max_bound {I V : Type*}
    (l : I → V) (K : Matrix V V ℂ) (o i : V) (M C : ℝ) (hM : 0 ≤ M)
    (hroot : ∀ a, ‖K o (l a)‖ ≤ M) (hrow : ∀ a, ‖K i (l a)‖ ≤ C) (a : I) :
    ‖K o (l a) * K i (l a)‖ ≤ M * C := by
  rw [norm_mul]
  exact mul_le_mul (hroot a) (hrow a) (norm_nonneg _) hM

end LocalLaw
