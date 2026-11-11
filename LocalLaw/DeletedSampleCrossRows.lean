import LocalLaw.DeletedSampleCrossBound
import LocalLaw.BlockSchurRows
import LocalLaw.DeficientGraphInstanceTransport

/-! # Actual full-kernel sampled rows from common cut and sampled-block rows -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance deletedSampleCrossRowsDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace DeficientGraph
variable {V:Type} [Fintype V] [DecidableEq V] {d:ℕ}

theorem deleted_sample_cross_rows (g:DeficientGraph V d)(hd:3≤d)(T:Set V)
    (q z:ℂ)(hz:0<z.im)(hq:0≤q.im)(a C:ℝ)(hC:0≤C)
    (hcut:letI : DecidableEq (Tᶜ:Set V):=fun a b=>Classical.propDecidable (a=b)
      ∀x:(Tᶜ:Set V),(∑j:T,‖((g.delete T).extensionGreen q z*g.H.submatrix
        (Subtype.val:(Tᶜ:Set V)→V) (Subtype.val:T→V)) x j‖)≤a)
    (hB:∀j:T,∑k:T,‖g.extensionGreen q z j.val k.val‖≤C) :
    ∀x:(Tᶜ:Set V),∑j:T,‖g.extensionGreen q z x.val j.val‖≤a*C := by
  let e:((Tᶜ:Set V)⊕T)≃V:=(Equiv.sumComm _ _).trans (Equiv.Set.sumCompl T)
  let M:Matrix ((Tᶜ:Set V)⊕T) ((Tᶜ:Set V)⊕T) ℂ:=(g.extensionMatrix q z).submatrix e e
  have hM:IsUnit M:=(Matrix.isUnit_submatrix_equiv e e).mpr (g.extensionMatrix_isUnit hd q z hz hq)
  have hcore:M.toBlocks₁₁=(g.delete T).extensionMatrix q z:=by
    rw [g.extensionMatrix_delete]
    ext i j
    rfl
  have hcu:IsUnit M.toBlocks₁₁:=hcore ▸ (g.delete T).extensionMatrix_isUnit hd q z hz hq
  have hcross:M.toBlocks₁₂=g.H.submatrix (Subtype.val:(Tᶜ:Set V)→V) (Subtype.val:T→V):=
    g.extensionMatrix_cross21 T q z
  have hi:M⁻¹=(g.extensionGreen q z).submatrix e e:=Matrix.inv_submatrix_equiv (g.extensionMatrix q z) e e
  have hcut':∀x:(Tᶜ:Set V),(∑j:T,‖(M.toBlocks₁₁⁻¹*M.toBlocks₁₂) x j‖)≤a:=by
    rw [hcore,hcross]
    have he:=extensionGreen_decidableEq_eq (g.delete T)
      (fun a b=>Classical.propDecidable (a=b)) inferInstance q z
    rw [he] at hcut
    exact hcut
  have hB':∀j:T,∑k:T,‖(M⁻¹).toBlocks₂₂ j k‖≤C:=by
    rw [hi]
    exact hB
  have hr:=rectangular_product_row_sum_bound (M.toBlocks₁₁⁻¹*M.toBlocks₁₂) (M⁻¹).toBlocks₂₂
    a C hC hcut' hB'
  intro x
  have he:=inverse_block12_from_core M hM hcu
  have he':(M⁻¹).toBlocks₁₂= -(M.toBlocks₁₁⁻¹*M.toBlocks₁₂*(M⁻¹).toBlocks₂₂):=he
  have hrow:(∑j:T,‖(M⁻¹).toBlocks₁₂ x j‖)≤a*C:=by
    rw [he']
    simpa only [Matrix.neg_apply,norm_neg] using hr x
  rw [hi] at hrow
  exact hrow

end DeficientGraph
end LocalLaw
