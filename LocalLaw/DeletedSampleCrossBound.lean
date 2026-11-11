import LocalLaw.BlockFarSampleColumn
import LocalLaw.PrincipalDeletion
import LocalLaw.BoundarySchurRows

/-! # Actual target-to-sampled correlations through the deleted core -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance deletedSampleCrossDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace DeficientGraph
variable {V:Type} [Fintype V] [DecidableEq V] {d:ℕ}

theorem deleted_sample_cross_bound (g:DeficientGraph V d)(hd:3≤d)(T:Set V)
    (q z:ℂ)(hz:0<z.im)(hq:0≤q.im)(x:(Tᶜ:Set V))(b:T)(K δ f a:ℝ)
    (hK:0≤K)(hδ:0≤δ)(hf:0≤f)
    (hdiag:‖g.extensionGreen q z b.val b.val‖≤K)
    (hoff:∀j:T,j≠b→‖g.extensionGreen q z j.val b.val‖≤δ)
    (hfar:‖((g.delete T).extensionGreen q z*g.H.submatrix
      (Subtype.val:(Tᶜ:Set V)→V) (Subtype.val:T→V)) x b‖≤f)
    (hL1:(∑j:T,‖((g.delete T).extensionGreen q z*g.H.submatrix
      (Subtype.val:(Tᶜ:Set V)→V) (Subtype.val:T→V)) x j‖)≤a) :
    ‖g.extensionGreen q z x.val b.val‖≤K*f+δ*a := by
  let e:((Tᶜ:Set V)⊕T)≃V:=(Equiv.sumComm _ _).trans (Equiv.Set.sumCompl T)
  let M:Matrix ((Tᶜ:Set V)⊕T) ((Tᶜ:Set V)⊕T) ℂ:=
    (g.extensionMatrix q z).submatrix e e
  have heCore (i:(Tᶜ:Set V)):e (.inl i)=i.val:=rfl
  have heSample (j:T):e (.inr j)=j.val:=rfl
  have hM:IsUnit M:=(Matrix.isUnit_submatrix_equiv e e).mpr (g.extensionMatrix_isUnit hd q z hz hq)
  have hcore:M.toBlocks₁₁=(g.delete T).extensionMatrix q z:=by
    rw [g.extensionMatrix_delete]
    ext i j
    rfl
  have hcu:IsUnit M.toBlocks₁₁:=by
    rw [hcore]
    exact (g.delete T).extensionMatrix_isUnit hd q z hz hq
  have hcross:M.toBlocks₁₂=g.H.submatrix (Subtype.val:(Tᶜ:Set V)→V) (Subtype.val:T→V):=by
    have hh:=g.extensionMatrix_cross21 T q z
    exact hh
  have hi:M⁻¹=(g.extensionGreen q z).submatrix e e:=Matrix.inv_submatrix_equiv (g.extensionMatrix q z) e e
  have hdiagM:‖(M⁻¹).toBlocks₂₂ b b‖≤K:=by
    rw [hi]
    exact hdiag
  have hoffM:∀j:T,j≠b→‖(M⁻¹).toBlocks₂₂ j b‖≤δ:=by
    rw [hi]
    exact hoff
  have hfarM:‖(M.toBlocks₁₁⁻¹*M.toBlocks₁₂) x b‖≤f:=by
    rw [hcore,hcross]
    exact hfar
  have hL1M:(∑j:T,‖(M.toBlocks₁₁⁻¹*M.toBlocks₁₂) x j‖)≤a:=by
    rw [hcore,hcross]
    exact hL1
  have hh:=inverse_block12_far_column M hM hcu x b K δ f a hK hδ hf hdiagM hoffM hfarM hL1M
  rw [hi] at hh
  exact hh

end DeficientGraph
end LocalLaw
