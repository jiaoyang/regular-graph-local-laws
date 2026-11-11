import LocalLaw.FarDeletionTarget

/-! # Deletion corrections retain the true target row sum -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance deletedTargetL1Decidable (p:Prop):Decidable p:=Classical.propDecidable p

theorem schurBilinear_bound_of_left_mass {I:Type} [Fintype I]
    (a b:I→ℂ)(R:Matrix I I ℂ)(A B C:ℝ)
    (_hA:0≤A)(hB:0≤B)(hC:0≤C)
    (ha:(∑i,‖a i‖)≤A)(hb:∀j,‖b j‖≤B)(hR:∀i,∑j,‖R i j‖≤C) :
    ‖schurBilinear a R b‖≤A*C*B := by
  have hinner (i:I):(∑j,‖R i j‖*‖b j‖)≤C*B:=by
    calc
      _≤∑j,‖R i j‖*B:=Finset.sum_le_sum (fun j _=>mul_le_mul_of_nonneg_left (hb j) (norm_nonneg _))
      _=(∑j,‖R i j‖)*B:=(Finset.sum_mul ..).symm
      _≤C*B:=mul_le_mul_of_nonneg_right (hR i) hB
  calc
    _≤∑i,∑j,‖a i‖*‖R i j‖*‖b j‖:=by
      unfold schurBilinear
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _=>by
        simpa only [norm_mul] using norm_sum_le Finset.univ (fun j=>a i*R i j*b j)))
    _=∑i,‖a i‖*(∑j,‖R i j‖*‖b j‖):=by simp only [Finset.mul_sum,mul_assoc]
    _≤∑i,‖a i‖*(C*B):=Finset.sum_le_sum (fun i _=>mul_le_mul_of_nonneg_left (hinner i) (norm_nonneg _))
    _=(∑i,‖a i‖)*(C*B):=(Finset.sum_mul ..).symm
    _≤A*(C*B):=mul_le_mul_of_nonneg_right ha (mul_nonneg hC hB)
    _=A*C*B:=by ring

namespace DeficientGraph
variable {V:Type} [Fintype V] [DecidableEq V] {d:ℕ}

theorem deleted_target_difference_left_mass (g:DeficientGraph V d)(hd:3≤d)
    (T:Set V)(q z:ℂ)(hz:0<z.im)(hq:0≤q.im)(C A B:ℝ)
    (hC:0≤C)(hA:0≤A)(hB:0≤B)
    (hrows:∀i:T,∑j:T,‖((g.extensionGreen q z).submatrix
      (Subtype.val:T→V) (Subtype.val:T→V))⁻¹ i j‖≤C)
    (x y:(Tᶜ:Set V))
    (hx:(∑i:T,‖g.extensionGreen q z x.val i.val‖)≤A)
    (hy:∀i:T,‖g.extensionGreen q z i.val y.val‖≤B) :
    ‖g.extensionGreen q z x.val y.val-(g.delete T).extensionGreen q z x y‖≤A*C*B := by
  let G:=g.extensionGreen q z
  let R:=(G.submatrix (Subtype.val:T→V) (Subtype.val:T→V))⁻¹
  have hh:=congrArg (fun M:Matrix (Tᶜ:Set V) (Tᶜ:Set V) ℂ=>M x y)
    (g.extensionGreen_delete hd T q z hz hq)
  dsimp only at hh
  simp only [Matrix.sub_apply,Matrix.mul_apply,Matrix.submatrix_apply,Finset.sum_mul] at hh
  rw [Finset.sum_comm] at hh
  have he:G x.val y.val-(g.delete T).extensionGreen q z x y=
      schurBilinear (fun i:T=>G x.val i.val) R (fun i:T=>G i.val y.val):=by
    unfold schurBilinear
    change (g.delete T).extensionGreen q z x y=G x.val y.val-_ at hh
    linear_combination -hh
  change ‖G x.val y.val-(g.delete T).extensionGreen q z x y‖≤_
  rw [he]
  exact schurBilinear_bound_of_left_mass _ _ R A B C hA hB hC hx hy hrows

end DeficientGraph
end LocalLaw
