import LocalLaw.RadialCavityRecursion
import LocalLaw.RegularTree
import SpectralConsequences.TrivialCorrections

/-! The source regular-root function X_ell, with its exact finite-tree meaning. -/
noncomputable section
namespace SpectralConsequences
open LocalLaw

/-- The regular-root analogue of the cavity iterate. A radius ell regular ball
has d branches whose root cavities have undergone ell iterations. -/
def regularRootValue (d ell:ℕ)(q z:ℂ):ℂ:=
  kestenMcKayTransform d (cavityIterate z q ell) z

theorem regularRootValue_fixed (d ell:ℕ)(m z:ℂ)(hm:m^2+z*m+1=0):
    regularRootValue d ell m z=kestenMcKayTransform d m z:=by
  simp only [regularRootValue,cavityIterate_fixed_point hm]

theorem regularRootValue_denominator_nonzero (d ell:ℕ)(q z:ℂ)
    (hz:0<z.im)(hq:0≤q.im):
    -z-(d:ℂ)/((d-1:ℕ):ℂ)*cavityIterate z q ell≠0:=
  kestenMcKay_denominator_ne_zero d _ z hz (cavityIterate_im_nonnegative z q hz hq ell)

/-- Genuine finite matrix inverse: no root identity or matrix unit is assumed. -/
theorem regularTreeMatrix_inverse_root (d n:ℕ)(hd:3≤d)(q z:ℂ)
    (hz:0<z.im)(hq:0≤q.im):
    IsUnit (regularTreeMatrix d n z q) ∧
      (regularTreeMatrix d n z q)⁻¹ (Sum.inl ()) (Sum.inl ())=regularRootValue d (n+1) q z:=by
  have hk:0<d-1:=by omega
  obtain ⟨hu,hg⟩:=cavityTree_inverse_root (d-1) (normalizedCavityEdge (d-1)) z q
    (normalizedCavityEdge_normalization (d-1) hk) n
    (fun j _=>cavityIterate_step_nonzero z q hz hq j)
  have hschur:rootSchurValue (-z)
      (branchRootCoupling d (cavityTreeRoot (d-1) n) (normalizedCavityEdge (d-1)))
      (identicalBranches d (cavityTreeMatrix (d-1) (normalizedCavityEdge (d-1)) z q n))=
      -z-(d:ℂ)/((d-1:ℕ):ℂ)*cavityIterate z q (n+1):=by
    rw [rootSchurValue,identicalBranches_self_energy d _ hu,
      normalizedCavityEdge_sq (d-1) hk,hg]
    ring
  have hh:=rootBlock_inverse_root (-z)
    (branchRootCoupling d (cavityTreeRoot (d-1) n) (normalizedCavityEdge (d-1)))
    (identicalBranches d (cavityTreeMatrix (d-1) (normalizedCavityEdge (d-1)) z q n))
    (identicalBranches_isUnit d _ hu)
    (by rw [hschur];exact regularRootValue_denominator_nonzero d (n+1) q z hz hq)
  exact ⟨hh.1,by simpa only [hschur,regularRootValue,kestenMcKayTransform] using hh.2⟩

/-- Exact denominator for regular-root linear response. -/
def regularRootDenominator (d ell:ℕ)(m md δ:ℂ):ℂ:=
  1-(m*cavitySum m ell+(d:ℂ)/((d-1:ℕ):ℂ)*md*m^(2*ell))*δ

/-- Exact fractional-linear response, with physical nonvanishing justified by
both inverse denominators. It has no Taylor remainder. -/
theorem regularRootValue_exact (d ell:ℕ)(m q z:ℂ)
    (hm:m^2+z*m+1=0)(hz:0<z.im)(hq:0≤q.im)(hmim:0 ≤ m.im)
    (hD:∀j≤ell,cavityDenominator m (q-m) j≠0):
    regularRootValue d ell q z-kestenMcKayTransform d m z=
      regularRootLinearCoefficient d ell m (kestenMcKayTransform d m z)*(q-m)/
        regularRootDenominator d ell m (kestenMcKayTransform d m z) (q-m):=by
  let c:ℂ:=(d:ℂ)/((d-1:ℕ):ℂ)
  let D:=cavityDenominator m (q-m) ell
  let md:=kestenMcKayTransform d m z
  have hden:D≠0:=hD ell le_rfl
  have hmd:-z-c*m≠0:=kestenMcKay_denominator_ne_zero d m z hz hmim
  have hqden:-z-c*cavityIterate z q ell≠0:=regularRootValue_denominator_nonzero d ell q z hz hq
  have hY:=cavity_iterate_exact hm ell hD
  have hmd0:md≠0:=inv_ne_zero hmd
  have hmdprod:(-z-c*m)*md=1:=mul_inv_cancel₀ hmd
  have hYprod:D*(cavityIterate z q ell-m)=m^(2*ell)*(q-m):=by
    rw [hY]
    change D*(m+m^(2*ell)*(q-m)/D-m)=m^(2*ell)*(q-m)
    field_simp [hden]
    ring
  have hED:regularRootDenominator d ell m md (q-m)=D-c*md*m^(2*ell)*(q-m):=by
    dsimp only [regularRootDenominator,D,cavityDenominator,c]
    ring
  have hE:regularRootDenominator d ell m md (q-m)=md*D*(-z-c*cavityIterate z q ell):=by
    rw [hED]
    linear_combination -D*hmdprod+(c*md)*hYprod
  have halg (R S a b t δ c y m:ℂ)(hR:R≠0)(ha:a≠0)(hb:b≠0)
      (hSa:S*a=1)(hSR:S-R=c*(y-m))(hY:b*(y-m)=t*δ):
      R⁻¹-a=c*a^2*t*δ/(a*b*R):=by
    apply (eq_div_iff (mul_ne_zero (mul_ne_zero ha hb) hR)).2
    have hRi:R⁻¹*R=1:=inv_mul_cancel₀ hR
    calc
      (R⁻¹-a)*(a*b*R)=a*b-a^2*b*R:=by linear_combination a*b*hRi
      _=a^2*b*(S-R):=by linear_combination -(a*b)*hSa
      _=c*a^2*(b*(y-m)):=by rw [hSR];ring
      _=c*a^2*t*δ:=by rw [hY];ring
  change (-z-c*cavityIterate z q ell)⁻¹-md=_
  rw [hE]
  exact halg _ (-z-c*m) md D (m^(2*ell)) (q-m) c _ m hqden hmd0 hden hmdprod
    (by ring) hYprod

end SpectralConsequences
#print axioms SpectralConsequences.regularTreeMatrix_inverse_root
#print axioms SpectralConsequences.regularRootValue_exact
