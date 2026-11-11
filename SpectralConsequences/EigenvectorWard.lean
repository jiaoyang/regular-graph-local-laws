import LocalLaw.FiniteModel

/-! # An eigenvector coordinate criterion from Ward's identity

This deterministic consequence applies to every finite Hermitian matrix and
any eigenvector, with its actual squared norm retained. It does not assume a
local law, probability estimate, or source eigenvector theorem.
-/

open scoped BigOperators
open Matrix
noncomputable section
namespace SpectralConsequences
variable {V:Type}[Fintype V][DecidableEq V]
open LocalLaw

/-- A real eigenvector equation and Ward's identity control every coordinate.
The vector may be zero or unnormalized. -/
theorem eigenvector_coordinate_sq_le_green_im_mul_sum (H:Matrix V V ℂ)(hH:H.IsHermitian)
    (eig η:ℝ)(hη:0<η)(v:V→ℂ)(heig:H *ᵥ v=(eig:ℂ) • v)
    (i:V):
    ‖v i‖^2≤η*(green H ((eig:ℂ)+(η:ℂ)*Complex.I) i i).im*(∑j,‖v j‖^2):=by
  classical
  let z:ℂ:=(eig:ℂ)+(η:ℂ)*Complex.I
  have hz:0<z.im:=by simpa only[z,Complex.add_im,Complex.ofReal_im,Complex.mul_im,
    Complex.ofReal_re,Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_add] using hη
  have hs:(spectralMatrix H z) *ᵥ v=((eig:ℂ)-z) • v:=by
    rw [spectralMatrix,Matrix.sub_mulVec,Matrix.smul_mulVec_assoc,Matrix.one_mulVec,heig,sub_smul]
  have hi:=congrArg (fun w:V→ℂ=>green H z *ᵥ w) hs
  dsimp only at hi
  rw [Matrix.mulVec_mulVec,green_mul_spectralMatrix H hH z hz,Matrix.one_mulVec,Matrix.mulVec_smul] at hi
  have hc:‖(eig:ℂ)-z‖=η:=by
    have he:(eig:ℂ)-z= -(η:ℂ)*Complex.I:=by dsimp only[z];ring
    rw [he,norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hη,Complex.norm_I,mul_one]
  have hn:‖v i‖=η*‖(green H z *ᵥ v) i‖:=by
    have h:=congrArg (fun w:V→ℂ=>‖w i‖) hi
    simpa only[Pi.smul_apply,smul_eq_mul,norm_mul,hc] using h
  have hsum:‖(green H z *ᵥ v) i‖≤∑j,‖green H z i j‖*‖v j‖:=by
    simpa only [Matrix.mulVec,dotProduct,norm_mul] using norm_sum_le Finset.univ (fun j=>green H z i j*v j)
  have hcs:=Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ:Finset V) (fun j=>‖green H z i j‖) (fun j=>‖v j‖)
  have hsq:‖(green H z *ᵥ v) i‖^2≤(∑j,‖green H z i j‖^2)*(∑j,‖v j‖^2):=by
    have hh:=mul_self_le_mul_self (norm_nonneg _) hsum
    have hh':‖(green H z *ᵥ v) i‖^2≤(∑j,‖green H z i j‖*‖v j‖)^2:=by simpa only[pow_two] using hh
    exact hh'.trans hcs
  calc
    _=η^2*‖(green H z *ᵥ v) i‖^2:=by rw[hn,mul_pow]
    _≤η^2*((∑j,‖green H z i j‖^2)*(∑j,‖v j‖^2)):=mul_le_mul_of_nonneg_left hsq (sq_nonneg η)
    _=η^2*(((green H z i i).im/η)*(∑j,‖v j‖^2)):=by
      rw[ward_identity H hH z hz i]
      simp only[z,Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,
        Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_add]
    _=η*(green H z i i).im*(∑j,‖v j‖^2):=by field_simp [ne_of_gt hη];ring

/-- The normalized form of the deterministic eigenvector criterion. -/
theorem normalized_eigenvector_coordinate_sq_le_green_im (H:Matrix V V ℂ)(hH:H.IsHermitian)
    (eig η:ℝ)(hη:0<η)(v:V→ℂ)(heig:H *ᵥ v=(eig:ℂ) • v)
    (hnorm:∑j,‖v j‖^2=1)(i:V):
    ‖v i‖^2≤η*(green H ((eig:ℂ)+(η:ℂ)*Complex.I) i i).im:=by
  simpa only[hnorm,mul_one] using eigenvector_coordinate_sq_le_green_im_mul_sum H hH eig η hη v heig i

/-- A diagonal imaginary-part bound gives a coordinate estimate without
choosing an eigenbasis. -/
theorem eigenvector_coordinate_sq_le_of_green_im_bound (H:Matrix V V ℂ)(hH:H.IsHermitian)
    (eig η B:ℝ)(hη:0<η)(v:V→ℂ)(heig:H *ᵥ v=(eig:ℂ) • v)(i:V)
    (hbound:(green H ((eig:ℂ)+(η:ℂ)*Complex.I) i i).im≤B):
    ‖v i‖^2≤η*B*(∑j,‖v j‖^2):=by
  refine (eigenvector_coordinate_sq_le_green_im_mul_sum H hH eig η hη v heig i).trans ?_
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbound hη.le)
    (Finset.sum_nonneg (fun _ _=>sq_nonneg _))

end SpectralConsequences

#print axioms SpectralConsequences.eigenvector_coordinate_sq_le_green_im_mul_sum
#print axioms SpectralConsequences.normalized_eigenvector_coordinate_sq_le_green_im
#print axioms SpectralConsequences.eigenvector_coordinate_sq_le_of_green_im_bound
