import LocalLaw.FiniteStarComparison

/-! # Uniform core errors pay the two true harmonic row sums -/

open scoped BigOperators
namespace LocalLaw
variable {I J:Type} [Fintype I] [DecidableEq I]

theorem finite_star_uniform_error (GM GN:Matrix (I⊕J) (I⊕J) ℂ)(R P:Matrix I I ℂ)
    (hlift:GM-GN=(GM.submatrix id Sum.inl*R⁻¹)*(R-P)*(P⁻¹*GN.submatrix Sum.inl id))
    (x y:I⊕J)(δ A B:ℝ)(hδ:0≤δ)(hA:0≤A)(_hB:0≤B)
    (he:∀i j,‖(R-P) i j‖≤δ)
    (hleft:(∑i:I,‖(GM.submatrix id Sum.inl*R⁻¹) x i‖)≤A)
    (hright:(∑i:I,‖(P⁻¹*GN.submatrix Sum.inl id) i y‖)≤B) :
    ‖GM x y-GN x y‖≤δ*A*B := by
  let L:=GM.submatrix id Sum.inl*R⁻¹
  let U:=P⁻¹*GN.submatrix Sum.inl id
  have hfirst (j:I):‖(L*(R-P)) x j‖≤A*δ:=
    rectangular_product_row_bound L (R-P) x j A δ hδ hleft (fun i=>he i j)
  have hh:=rectangular_product_column_bound (L*(R-P)) U x y (A*δ) B
    (mul_nonneg hA hδ) hfirst hright
  change ‖(GM-GN) x y‖≤_
  rw [hlift]
  exact hh.trans_eq (by ring)

end LocalLaw
