import SpectralConsequences.PhysicalCrossDeletion

/-! # Schur cross transfer with an actual indexed removed set -/
open scoped BigOperators
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance indexedCrossDeletionDecidable (p:Prop):Decidable p:=Classical.propDecidable p
variable {V I:Type} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

theorem physical_indexed_deleted_entry_bound (H:Matrix V V ℂ) (hH:H.IsHermitian)
    (S:Set V) [DecidablePred (fun v=>v∈S)] (φ:I≃S) (z:ℂ) (hz:0<z.im)
    (P A B ε:ℝ) (hP:0≤P) (hA:0≤A) (hB:0≤B)
    (hrows:∀i,∑j,‖((green H z).submatrix (fun i=>(φ i).val) (fun i=>(φ i).val))⁻¹ i j‖≤P)
    (x y:(Sᶜ:Set V)) (hxy:‖green H z x.val y.val‖≤ε)
    (hx:∀i,‖green H z x.val (φ i).val‖≤A)
    (hy:∀i,‖green H z (φ i).val y.val‖≤B) :
    ‖green (H.submatrix (Subtype.val:(Sᶜ:Set V)→V) (Subtype.val:(Sᶜ:Set V)→V)) z x y‖≤
      ε+(Fintype.card I:ℝ)*P*A*B := by
  let U:=(green H z).submatrix (Subtype.val:S→V) (Subtype.val:S→V)
  have hm:U.submatrix φ φ=(green H z).submatrix (fun i=>(φ i).val) (fun i=>(φ i).val):=by ext i j;rfl
  have hi:((green H z).submatrix (fun i=>(φ i).val) (fun i=>(φ i).val))⁻¹=U⁻¹.submatrix φ φ:=by
    rw [←hm,Matrix.inv_submatrix_equiv]
  have hr:∀i:S,∑j:S,‖U⁻¹ i j‖≤P:=by
    intro i
    have hh:=hrows (φ.symm i)
    rw [hi] at hh
    simp only [Matrix.submatrix_apply,φ.apply_symm_apply] at hh
    rw [Equiv.sum_comp φ (fun j=>‖U⁻¹ i j‖)] at hh
    exact hh
  have hx':∀i:S,‖green H z x.val i.val‖≤A:=by
    intro i
    simpa only [φ.apply_symm_apply] using hx (φ.symm i)
  have hy':∀i:S,‖green H z i.val y.val‖≤B:=by
    intro i
    simpa only [φ.apply_symm_apply] using hy (φ.symm i)
  have hh:=physical_deleted_entry_bound H hH S z hz P A B ε hP hA hB hr x y hxy hx' hy'
  have hc:Fintype.card S=Fintype.card I:=(Fintype.card_congr φ).symm
  simpa only [hc] using hh

end SpectralConsequences
