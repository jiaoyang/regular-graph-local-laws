import Mathlib

/-! # Restrict a true nonnegative row sum to a vertex subset -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance subsetNormRowsDecidable (p:Prop):Decidable p:=Classical.propDecidable p

theorem sum_norm_subtype_le {V:Type} [Fintype V] (A B:Set V)(hAB:A⊆B)(f:V→ℂ) :
    (∑i:A,‖f i.val‖)≤∑j:B,‖f j.val‖ := by
  let e:A↪B:=
    {toFun:=fun i=>⟨i.val,hAB i.property⟩
     inj':=by
       intro u v h
       have hh:u.val=v.val:=congrArg (fun w:B=>w.val) h
       exact Subtype.ext hh}
  calc
    _=∑j∈Finset.univ.map e,‖f j.val‖:=by rw [Finset.sum_map];rfl
    _≤∑j:B,‖f j.val‖:=Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _=>norm_nonneg _)

end LocalLaw
