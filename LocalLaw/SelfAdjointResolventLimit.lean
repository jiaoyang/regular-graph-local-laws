import LocalLaw.BoundedGraphOperator

/-! # Strong convergence of genuine nonreal self-adjoint resolvents

The imaginary-part energy bound is proved explicitly. Strong convergence of
bounded self-adjoint adjacency truncations then implies strong resolvent
convergence, without a premise asserting convergence of Green functions.
-/

open Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 1800000
namespace LocalLaw
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def physicalSpectralOperator (A : E →L[ℂ] E) (z : ℂ) : E →L[ℂ] E := A-z • 1
def physicalResolvent (A : E →L[ℂ] E) (z : ℂ) : E →L[ℂ] E := Ring.inverse (physicalSpectralOperator A z)

theorem selfAdjoint_physicalSpectral_isUnit (A : E →L[ℂ] E) (hA : IsSelfAdjoint A)
    (z : ℂ) (hz : z.im≠0) : IsUnit (physicalSpectralOperator A z) := by
  have hnot : z∉spectrum ℂ A := fun h => hz (hA.im_eq_zero_of_mem_spectrum h)
  have hu := (spectrum.not_mem_iff.mp hnot).neg
  simpa only [Algebra.algebraMap_eq_smul_one,neg_sub] using hu

theorem physicalResolvent_right_inverse (A : E →L[ℂ] E) (hA : IsSelfAdjoint A)
    (z : ℂ) (hz : z.im≠0) (u : E) : physicalSpectralOperator A z (physicalResolvent A z u)=u := by
  have h := Ring.mul_inverse_cancel _ (selfAdjoint_physicalSpectral_isUnit A hA z hz)
  exact congrArg (fun B : E →L[ℂ] E => B u) h

theorem selfAdjoint_inner_map_im_zero (A : E →L[ℂ] E) (hA : IsSelfAdjoint A) (v : E) :
    (@inner ℂ E _ v (A v)).im=0 := by
  have hs := congrArg Complex.im (hA.isSymmetric v v)
  have hc := inner_im_symm (𝕜:=ℂ) v (A v)
  change (@inner ℂ E _ (A v) v).im=(@inner ℂ E _ v (A v)).im at hs
  change (@inner ℂ E _ v (A v)).im= -(@inner ℂ E _ (A v) v).im at hc
  nlinarith only [hs,hc]

theorem selfAdjoint_spectral_energy_bound (A : E →L[ℂ] E) (hA : IsSelfAdjoint A)
    (z : ℂ) (hz : 0<z.im) (v : E) : z.im*‖v‖≤‖physicalSpectralOperator A z v‖ := by
  have him : (@inner ℂ E _ v (physicalSpectralOperator A z v)).im= -z.im*‖v‖^2 := by
    have hselfRe : (@inner ℂ E _ v v).re=‖v‖^2 := inner_self_eq_norm_sq (𝕜:=ℂ) v
    have hselfIm : (@inner ℂ E _ v v).im=0 := inner_self_im (𝕜:=ℂ) v
    simp only [physicalSpectralOperator,ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply,inner_sub_right,inner_smul_right,hselfRe,hselfIm,
      Complex.sub_im,Complex.mul_im,hselfRe,hselfIm,mul_zero,add_zero,
      selfAdjoint_inner_map_im_zero A hA]
    ring
  have hb := (Complex.abs_im_le_norm (@inner ℂ E _ v (physicalSpectralOperator A z v))).trans
    (norm_inner_le_norm v (physicalSpectralOperator A z v))
  rw [him,abs_mul,abs_neg,abs_of_pos hz,abs_of_nonneg (sq_nonneg _)] at hb
  by_cases hv : v=0
  · simp only [hv,norm_zero,mul_zero]
    exact norm_nonneg _
  · have hvp : 0<‖v‖ := norm_pos_iff.mpr hv
    apply (mul_le_mul_left hvp).mp
    nlinarith only [hb]

theorem physicalResolvent_apply_norm_bound (A : E →L[ℂ] E) (hA : IsSelfAdjoint A)
    (z : ℂ) (hz : 0<z.im) (u : E) : ‖physicalResolvent A z u‖≤‖u‖/z.im := by
  have h := selfAdjoint_spectral_energy_bound A hA z hz (physicalResolvent A z u)
  rw [physicalResolvent_right_inverse A hA z (ne_of_gt hz)] at h
  exact (le_div_iff₀ hz).mpr (by simpa only [mul_comm] using h)

theorem physicalResolvent_norm_bound (A : E →L[ℂ] E) (hA : IsSelfAdjoint A)
    (z : ℂ) (hz : 0<z.im) : ‖physicalResolvent A z‖≤z.im⁻¹ := by
  apply (physicalResolvent A z).opNorm_le_bound (by positivity)
  intro u
  exact (physicalResolvent_apply_norm_bound A hA z hz u).trans_eq (by ring)

theorem selfAdjoint_resolvents_tendsto_strong (A : E →L[ℂ] E) (hA : IsSelfAdjoint A)
    (An : ℕ → E →L[ℂ] E) (hAn : ∀ n,IsSelfAdjoint (An n))
    (hstrong : ∀ v : E,Tendsto (fun n => An n v) atTop (𝓝 (A v)))
    (z : ℂ) (hz : 0<z.im) (u : E) :
    Tendsto (fun n => physicalResolvent (An n) z u) atTop (𝓝 (physicalResolvent A z u)) := by
  let v := physicalResolvent A z u
  have hident (n : ℕ) : physicalSpectralOperator (An n) z (physicalResolvent (An n) z u-v)=A v-An n v := by
    rw [map_sub,physicalResolvent_right_inverse (An n) (hAn n) z (ne_of_gt hz)]
    have hv := physicalResolvent_right_inverse A hA z (ne_of_gt hz) u
    change A v-z • v=u at hv
    rw [←hv]
    simp only [physicalSpectralOperator,ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply]
    abel
  have hbound (n : ℕ) : ‖physicalResolvent (An n) z u-v‖≤‖A v-An n v‖/z.im := by
    have hh := selfAdjoint_spectral_energy_bound (An n) (hAn n) z hz (physicalResolvent (An n) z u-v)
    rw [hident] at hh
    exact (le_div_iff₀ hz).mpr (by simpa only [mul_comm] using hh)
  have hzero : Tendsto (fun n => ‖A v-An n v‖/z.im) atTop (𝓝 0) := by
    have h := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => A v) atTop (𝓝 (A v))).sub (hstrong v)).norm.div_const z.im
    simpa only [sub_self,norm_zero,zero_div] using h
  have hnorm := squeeze_zero (fun n => norm_nonneg (physicalResolvent (An n) z u-v)) hbound hzero
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hnorm

end LocalLaw
