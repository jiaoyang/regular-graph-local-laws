import LocalLaw.RegularTree
import LocalLaw.TreeReferenceKernel
import LocalLaw.Semicircle

/-! The explicit corrections in source (7.6) and (7.40).

The shared pole is that of the genuine constant eigenvector. The generic
coefficient forms keep its algebra separate from the upper-half-plane choice.
-/
noncomputable section
namespace SpectralConsequences
open LocalLaw

/-- Coefficient of the common pole in the cavity correction. -/
def cavityCorrectionCoefficient (d ell:ℕ)(m:ℂ):ℂ:=
  ((((d-1:ℕ):ℂ)^(ell+1))-1)*m^(2*ell+2)*(1+m*treeEdgeWeight d)^2

/-- Coefficient of the common pole in the trace correction. -/
def traceCorrectionCoefficient (d ell:ℕ)(m md:ℂ):ℂ:=
  (d:ℂ)/((d-1:ℕ):ℂ)*((d:ℂ)*((d-1:ℕ):ℂ)^ell-1)*
    md^2*m^(2*ell)*(1+m*treeEdgeWeight d)^2

/-- Linear response of the regular-root function X_ell at the physical root. -/
def regularRootLinearCoefficient (d ell:ℕ)(m md:ℂ):ℂ:=
  (d:ℂ)/((d-1:ℕ):ℂ)*md^2*m^(2*ell)

/-- The normalized resolvent pole of the constant eigenvector. -/
def trivialPole (N d:ℕ)(z:ℂ):ℂ:=
  (N:ℂ)⁻¹*((d:ℂ)*treeEdgeWeight d-z)⁻¹

def trivialCavityCorrection (N d ell:ℕ)(z:ℂ):ℂ:=
  cavityCorrectionCoefficient d ell (semicircleRoot z)*trivialPole N d z

def trivialTraceCorrection (N d ell:ℕ)(z:ℂ):ℂ:=
  traceCorrectionCoefficient d ell (semicircleRoot z)
    (kestenMcKayTransform d (semicircleRoot z) z)*trivialPole N d z

/-- Generic cancellation of the two linearized correction numerators.
This identity exposes exactly the remaining pole cancellation needed in (7.40). -/
theorem correction_combination_coefficient (d ell:ℕ)(hd:1≤d)(m md:ℂ)
    (hpow:1-m^(2*ell+2)≠0):
    traceCorrectionCoefficient d ell m md+
      regularRootLinearCoefficient d ell m md/(1-m^(2*ell+2))*cavityCorrectionCoefficient d ell m=
      regularRootLinearCoefficient d ell m md*(1+m*treeEdgeWeight d)^2*
        ((((d-1:ℕ):ℂ)^ell*((d:ℂ)-m^(2*ell+2))-1)/(1-m^(2*ell+2))):=by
  have hdcast:(d:ℂ)=((d-1:ℕ):ℂ)+1:=by exact_mod_cast (show d=d-1+1 by omega)
  have halg (A k K t s:ℂ)(ht:1-t≠0):
      A*((k+1)*K-1)*s^2+A/(1-t)*((k*K-1)*t*s^2)=
        A*s^2*((K*(k+1-t)-1)/(1-t)):=by
    field_simp [ht]
    ring
  have hh:=halg (regularRootLinearCoefficient d ell m md) ((d-1:ℕ):ℂ)
    (((d-1:ℕ):ℂ)^ell) (m^(2*ell+2)) (1+m*treeEdgeWeight d) hpow
  rw [←hdcast] at hh
  convert hh using 1
  · (simp only [traceCorrectionCoefficient,regularRootLinearCoefficient,cavityCorrectionCoefficient,pow_succ]; ring)

theorem correction_combination (N d ell:ℕ)(hd:1≤d)(z:ℂ)
    (hpow:1-(semicircleRoot z)^(2*ell+2)≠0):
    trivialTraceCorrection N d ell z+
      regularRootLinearCoefficient d ell (semicircleRoot z)
        (kestenMcKayTransform d (semicircleRoot z) z)/(1-(semicircleRoot z)^(2*ell+2))*
          trivialCavityCorrection N d ell z=
      (regularRootLinearCoefficient d ell (semicircleRoot z)
        (kestenMcKayTransform d (semicircleRoot z) z)*(1+semicircleRoot z*treeEdgeWeight d)^2*
        ((((d-1:ℕ):ℂ)^ell*((d:ℂ)-(semicircleRoot z)^(2*ell+2))-1)/
          (1-(semicircleRoot z)^(2*ell+2))))*trivialPole N d z:=by
  unfold trivialTraceCorrection trivialCavityCorrection
  calc
    _ = (traceCorrectionCoefficient d ell (semicircleRoot z) (kestenMcKayTransform d (semicircleRoot z) z)+
      regularRootLinearCoefficient d ell (semicircleRoot z) (kestenMcKayTransform d (semicircleRoot z) z)/
        (1-(semicircleRoot z)^(2*ell+2))*cavityCorrectionCoefficient d ell (semicircleRoot z))*trivialPole N d z:=by ring
    _ = _:=by rw [correction_combination_coefficient d ell hd _ _ hpow]

end SpectralConsequences
#print axioms SpectralConsequences.correction_combination
