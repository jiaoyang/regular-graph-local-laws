import SpectralConsequences.IndexedDeletionQuadratic

/-! # Schur cross-entry transfer through a small actual deletion -/
open scoped BigOperators
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance physicalCrossDeletionDecidable (p:Prop) : Decidable p := Classical.propDecidable p
variable {V:Type} [Fintype V] [DecidableEq V]

theorem physical_deleted_entry_bound (H:Matrix V V ℂ) (hH:H.IsHermitian)
    (S:Set V) [DecidablePred (fun v=>v∈S)] (z:ℂ) (hz:0<z.im)
    (P A B ε:ℝ) (hP:0≤P) (hA:0≤A) (hB:0≤B)
    (hrows:∀i:S,∑j:S,‖((green H z).submatrix (Subtype.val:S→V) (Subtype.val:S→V))⁻¹ i j‖≤P)
    (x y:(Sᶜ:Set V)) (hxy:‖green H z x.val y.val‖≤ε)
    (hx:∀i:S,‖green H z x.val i.val‖≤A)
    (hy:∀i:S,‖green H z i.val y.val‖≤B) :
    ‖green (H.submatrix (Subtype.val:(Sᶜ:Set V)→V) (Subtype.val:(Sᶜ:Set V)→V)) z x y‖≤
      ε+(Fintype.card S:ℝ)*P*A*B := by
  let G:=green H z
  let R:=((green H z).submatrix (Subtype.val:S→V) (Subtype.val:S→V))⁻¹
  have hh:=congrArg (fun M:Matrix (Sᶜ:Set V) (Sᶜ:Set V) ℂ=>M x y)
    (green_deleted_principal S H hH z hz)
  dsimp only at hh
  simp only [Matrix.sub_apply,Matrix.mul_apply,Matrix.submatrix_apply,Finset.sum_mul] at hh
  rw [Finset.sum_comm] at hh
  have he : green (H.submatrix (Subtype.val:(Sᶜ:Set V)→V) (Subtype.val:(Sᶜ:Set V)→V)) z x y=
      G x.val y.val-schurBilinear (fun i:S=>G x.val i.val) R (fun j:S=>G j.val y.val) := by
    unfold schurBilinear
    exact hh
  rw [he]
  exact (norm_sub_le _ _).trans (add_le_add hxy
    (schurBilinear_bound_of_row_mass _ _ R A B P hA hB hP hx hy hrows))

end SpectralConsequences
