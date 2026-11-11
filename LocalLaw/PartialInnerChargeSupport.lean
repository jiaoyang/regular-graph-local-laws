import LocalLaw.PartialInnerDiagonalChange
import LocalLaw.DiagonalChangeMappedRows

/-! The support of omitted inner charges has actual cut-boundary cardinality. -/
open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance partialInnerChargeSupportDecidable (p:Prop):Decidable p:=Classical.propDecidable p

theorem nat_card_support_le_sum {V:Type}[Fintype V](f:V→ℕ):
    Nat.card {v//f v≠0}≤∑v,f v:=by
  classical
  let e:({v//f v≠0})↪V:=Function.Embedding.subtype _
  calc
    _=∑_v:{v//f v≠0},1:=by simp [Nat.card_eq_fintype_card]
    _≤∑v:{v//f v≠0},f v.val:=Finset.sum_le_sum (fun v _=>Nat.one_le_iff_ne_zero.mpr v.property)
    _=∑v∈Finset.univ.image e,f v:=(Finset.sum_image (fun _ _ _ _ h=>e.injective h)).symm
    _≤_:=Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _=>Nat.zero_le _)

namespace DeficientGraph
variable {V:Type}[Fintype V]{d:ℕ}

theorem partialInnerOmittedCharge_support_card (g:DeficientGraph V d)(T S:Set V)(K:Set (Tᶜ:Set V)):
    Nat.card {v:K//g.partialInnerOmittedCharge T S v.val≠0}≤Nat.card (BoundaryOrientedEdge g.graph T):=
  (nat_card_support_le_sum _).trans (g.partialInnerOmittedCharge_sum_le_boundary T S K)

theorem partialInnerOmittedCharge_norm_le (g:DeficientGraph V d)(hd:3≤d)(T S:Set V)
    (q:ℂ)(hq:‖q‖≤2)(v:(Tᶜ:Set V)):
    ‖-q*(((g.partialInnerOmittedCharge T S v:ℝ)/((d:ℝ)-1)):ℂ)‖≤(d:ℝ):=by
  have hdR:(3:ℝ)≤d:=Nat.cast_le.mpr hd
  have hk:0<(d:ℝ)-1:=by linarith
  have hρ: (g.partialInnerOmittedCharge T S v:ℝ)≤d:=
    Nat.cast_le.mpr ((g.partialInnerOmittedCharge_le T S v).trans ((g.delete T).deficit_le v))
  have hratio:‖q‖/((d:ℝ)-1)≤1:=(div_le_one hk).mpr (hq.trans (by linarith))
  have hden:‖(d:ℂ)-1‖=(d:ℝ)-1:=by
    have hc:(d:ℂ)-1=(((d:ℝ)-1:ℝ):ℂ):=by push_cast;rfl
    rw [hc,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hk]
  have he:‖-q*(((g.partialInnerOmittedCharge T S v:ℝ)/((d:ℝ)-1)):ℂ)‖=
      (‖q‖/((d:ℝ)-1))*(g.partialInnerOmittedCharge T S v:ℝ):=by
    simp only [norm_mul,norm_neg,norm_div,Complex.ofReal_natCast,Complex.norm_natCast,Complex.ofReal_one]
    rw [hden]
    ring
  rw [he]
  exact (mul_le_mul_of_nonneg_right hratio (Nat.cast_nonneg _)).trans (by simpa only [one_mul] using hρ)

end DeficientGraph
end LocalLaw
