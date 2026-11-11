import LocalLaw.CoreSchurLift

/-! # Right harmonic weights are transposes of the left weights -/

namespace LocalLaw
variable {I J:Type} [Fintype I] [DecidableEq I]

theorem symmetric_core_lift_transpose (G:Matrix (I⊕J) (I⊕J) ℂ)(R:Matrix I I ℂ)
    (hG:G.IsSymm)(hR:R.IsSymm) :
    (G.submatrix id Sum.inl*R⁻¹).transpose=R⁻¹*G.submatrix Sum.inl id := by
  rw[Matrix.transpose_mul,Matrix.transpose_nonsing_inv,hR,Matrix.transpose_submatrix,hG]

theorem symmetric_core_lift_entry (G:Matrix (I⊕J) (I⊕J) ℂ)(R:Matrix I I ℂ)
    (hG:G.IsSymm)(hR:R.IsSymm)(u:I)(x:I⊕J) :
    (R⁻¹*G.submatrix Sum.inl id) u x=(G.submatrix id Sum.inl*R⁻¹) x u :=
  (congrArg (fun A:Matrix I (I⊕J) ℂ=>A u x) (symmetric_core_lift_transpose G R hG hR)).symm

end LocalLaw
