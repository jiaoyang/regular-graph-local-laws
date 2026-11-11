import LocalLaw.BlockSchurRows

/-! # Block inverse rows with bounded branching on the core side -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
variable {I J:Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem block_inverse_row_sum_bound_asymmetric (M:Matrix (I⊕J) (I⊕J) ℂ)
    (hM:IsUnit M) (hD:IsUnit M.toBlocks₂₂) (C p a:ℝ) (hC:0≤C) (hp:0≤p) (ha:0≤a)
    (hS:∀i,∑k,‖(blockSchur M)⁻¹ i k‖≤C)
    (hDrows:∀j,∑k,‖M.toBlocks₂₂⁻¹ j k‖≤p)
    (hL:∀i,∑j,‖(M.toBlocks₁₂*M.toBlocks₂₂⁻¹) i j‖≤a)
    (hR:∀j,∑i,‖(M.toBlocks₂₂⁻¹*M.toBlocks₂₁) j i‖≤1) :
    ∀u,∑v,‖M⁻¹ u v‖≤p+(1+a)*C := by
  let X:=(blockSchur M)⁻¹
  let D:=M.toBlocks₂₂⁻¹
  let L:=M.toBlocks₁₂*D
  let R:=D*M.toBlocks₂₁
  have hform:M⁻¹=Matrix.fromBlocks X (-(X*L)) (-(R*X)) (D+R*X*L):=by
    simpa only [X,D,L,R,Matrix.mul_assoc] using block_inverse_formula M hM hD
  have hXL:∀i,∑j,‖(X*L) i j‖≤C*a:=rectangular_product_row_sum_bound X L C a ha hS hL
  have hRX:∀j,∑i,‖(R*X) j i‖≤1*C:=rectangular_product_row_sum_bound R X 1 C hC hR hS
  have hRXL:∀j,∑k,‖(R*X*L) j k‖≤(1*C)*a:=
    rectangular_product_row_sum_bound (R*X) L (1*C) a ha hRX hL
  have hbottom (j:J):(∑k,‖(D+R*X*L) j k‖)≤p+(1*C)*a:=by
    calc
      _≤∑k,(‖D j k‖+‖(R*X*L) j k‖):=Finset.sum_le_sum (fun k _=>norm_add_le _ _)
      _=_:=Finset.sum_add_distrib
      _≤_:=add_le_add (hDrows j) (hRXL j)
  intro u
  rw [hform]
  cases u with
  | inl i =>
    simp only [Fintype.sum_sum_type,Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,Matrix.neg_apply,norm_neg]
    have hh:=add_le_add (hS i) (hXL i)
    nlinarith only [hh,hp]
  | inr j =>
    simp only [Fintype.sum_sum_type,Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,Matrix.neg_apply,norm_neg]
    have hh:=add_le_add (hRX j) (hbottom j)
    nlinarith only [hh]

end LocalLaw
