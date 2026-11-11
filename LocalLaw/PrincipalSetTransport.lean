import LocalLaw.EmbeddedPrincipalRows

/-! # Principal inverse caps are independent of finite-set presentations -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance principalSetTransportDecidable (p:Prop):Decidable p:=Classical.propDecidable p
variable {V:Type} [Fintype V]

theorem principal_inverse_caps_set_congr (A:Matrix V V ℂ)(S T:Set V)
    [FS:Fintype S] [FT:Fintype T] [DS:DecidableEq S] [DT:DecidableEq T]
    (h:S=T)(C:ℝ)
    (hs:let P:=A.submatrix (Subtype.val:S→V) (Subtype.val:S→V);
      IsUnit P ∧ (∀i,∑j,‖P⁻¹ i j‖≤C) ∧ (∀j,∑i,‖P⁻¹ i j‖≤C)) :
    let P:=A.submatrix (Subtype.val:T→V) (Subtype.val:T→V);
      IsUnit P ∧ (∀i,∑j,‖P⁻¹ i j‖≤C) ∧ (∀j,∑i,‖P⁻¹ i j‖≤C) := by
  cases h
  cases Subsingleton.elim FS FT
  cases Subsingleton.elim DS DT
  exact hs

end LocalLaw
