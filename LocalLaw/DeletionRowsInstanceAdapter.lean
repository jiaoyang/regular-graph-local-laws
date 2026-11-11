import LocalLaw.FarDeletionTarget
import LocalLaw.DeletedTargetL1

/-! # Inverse-row transport before actual deletion estimates

Fintype enumerations and equality decisions do not change the inverse-row
bound. Transport them while the index type is abstract.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
set_option maxHeartbeats 500000
local instance deletionRowsInstanceAdapterDecidable (p:Prop):Decidable p:=Classical.propDecidable p

def MatrixInverseRowsBound {I:Type} [Fintype I] [DecidableEq I]
    (M:Matrix I I ℂ)(C:ℝ):Prop:=∀i,∑j,‖M⁻¹ i j‖≤C

theorem matrix_inverse_rows_instances {I:Type}(F₁ F₂:Fintype I)(D₁ D₂:DecidableEq I)
    (M:Matrix I I ℂ)(C:ℝ)(h:@MatrixInverseRowsBound I F₁ D₁ M C) :
    @MatrixInverseRowsBound I F₂ D₂ M C := by
  cases Subsingleton.elim F₁ F₂
  cases Subsingleton.elim D₁ D₂
  exact h

def deletionSetFintype {V:Type} [Fintype V] (T:Set V):Fintype T:=inferInstance

def deletionSetDecidableEq {V:Type} [DecidableEq V] (T:Set V):DecidableEq T:=inferInstance

namespace DeficientGraph
variable {V:Type} [Fintype V] [DecidableEq V] {d:ℕ}

theorem far_deleted_target_difference_any_rows (g:DeficientGraph V d)(hd:3≤d)
    (T:Set V)(q z:ℂ)(hz:0<z.im)(hq:0≤q.im)(C a b:ℝ)
    (hC:0≤C)(ha:0≤a)(hb:0≤b)(FT:Fintype T)(DT:DecidableEq T)
    (hrows:@MatrixInverseRowsBound T FT DT ((g.extensionGreen q z).submatrix
      (Subtype.val:T→V) (Subtype.val:T→V)) C)
    (x y:(Tᶜ:Set V))
    (hx:∀i:T,‖g.extensionGreen q z x.val i.val‖≤a)
    (hy:∀i:T,‖g.extensionGreen q z i.val y.val‖≤b) :
    ‖g.extensionGreen q z x.val y.val-(g.delete T).extensionGreen q z x y‖≤
      (Fintype.card T:ℝ)*C*a*b := by
  have hFT:FT=deletionSetFintype T:=Subsingleton.elim _ _
  subst FT
  have hDT:DT=deletionSetDecidableEq T:=Subsingleton.elim _ _
  subst DT
  dsimp only [MatrixInverseRowsBound] at hrows
  exact g.far_deleted_target_difference hd T q z hz hq C a b hC ha hb hrows x y hx hy

theorem deleted_target_difference_left_mass_any_rows (g:DeficientGraph V d)(hd:3≤d)
    (T:Set V)(q z:ℂ)(hz:0<z.im)(hq:0≤q.im)(C A B:ℝ)
    (hC:0≤C)(hA:0≤A)(hB:0≤B)(FT:Fintype T)(DT:DecidableEq T)
    (hrows:@MatrixInverseRowsBound T FT DT ((g.extensionGreen q z).submatrix
      (Subtype.val:T→V) (Subtype.val:T→V)) C)
    (x y:(Tᶜ:Set V))
    (hx:(∑i:T,‖g.extensionGreen q z x.val i.val‖)≤A)
    (hy:∀i:T,‖g.extensionGreen q z i.val y.val‖≤B) :
    ‖g.extensionGreen q z x.val y.val-(g.delete T).extensionGreen q z x y‖≤A*C*B := by
  have hFT:FT=deletionSetFintype T:=Subsingleton.elim _ _
  subst FT
  have hDT:DT=deletionSetDecidableEq T:=Subsingleton.elim _ _
  subst DT
  dsimp only [MatrixInverseRowsBound] at hrows
  exact g.deleted_target_difference_left_mass hd T q z hz hq C A B hC hA hB hrows x y hx hy

end DeficientGraph
end LocalLaw
