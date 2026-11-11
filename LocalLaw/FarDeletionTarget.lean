import LocalLaw.AttachedLeafTargetBound
import LocalLaw.BoundarySchurRows

/-! # Genuine target deletion cost for a far omitted vertex set -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance farDeletionTargetDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace DeficientGraph
variable {V:Type} [Fintype V] [DecidableEq V] {d:ℕ}

theorem far_deleted_target_difference (g:DeficientGraph V d)(hd:3≤d)
    (T:Set V)(q z:ℂ)(hz:0<z.im)(hq:0≤q.im)(C a b:ℝ)
    (hC:0≤C)(ha:0≤a)(hb:0≤b)
    (hrows:∀i:T,∑j:T,‖((g.extensionGreen q z).submatrix
      (Subtype.val:T→V) (Subtype.val:T→V))⁻¹ i j‖≤C)
    (x y:(Tᶜ:Set V))
    (hx:∀i:T,‖g.extensionGreen q z x.val i.val‖≤a)
    (hy:∀i:T,‖g.extensionGreen q z i.val y.val‖≤b) :
    ‖g.extensionGreen q z x.val y.val-(g.delete T).extensionGreen q z x y‖≤
      (Fintype.card T:ℝ)*C*a*b := by
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
  exact schurBilinear_bound_of_row_mass _ _ R a b C ha hb hC hx hy hrows

end DeficientGraph
end LocalLaw
