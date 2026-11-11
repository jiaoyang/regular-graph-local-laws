import LocalLaw.SmallSampleKernelRestoration

/-! # Polynomial coefficients for the restored full kernel -/
open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance smallSampleKernelDecayDecidable (p:Prop):Decidable p:=Classical.propDecidable p

def smallSampleKernelCoefficient (d:ℕ)(K C D:ℝ):ℝ:=
  let U:=4*(d:ℝ)*K
  K+4*U*C*(d:ℝ)*K+C*(d:ℝ)*K+2*D*U^2+D*U+D+1

private theorem smallSample_polynomial_bound (d:ℕ)(K C D L ε t:ℝ)
    (hK:0≤K)(hC:0≤C)(hD:0≤D)(hL:1≤L)(hε:0≤ε)(ht:0≤t) :
    let F:=K*L*t+K*L*ε
    let f:=F*(d:ℝ)
    let a:=4*(d:ℝ)*K*L
    F+2*(f*(a*C)+a*(C*f+(D*L*ε)*a))+(C*f+(D*L*ε)*a)+D*L*ε≤
      smallSampleKernelCoefficient d K C D*L^2*t+smallSampleKernelCoefficient d K C D*L^3*ε := by
  dsimp only
  let U:=4*(d:ℝ)*K
  have hU:0≤U:=by dsimp only[U];positivity
  have hL0:0≤L:=by linarith
  have hL2:L≤L^2:=by nlinarith
  have hL23:L^2≤L^3:=by nlinarith [mul_nonneg (sq_nonneg L) (sub_nonneg.mpr hL)]
  have hL3:L≤L^3:=hL2.trans hL23
  calc
    _=K*L*t+K*L*ε+(4*U*C*(d:ℝ)*K)*L^2*t+(4*U*C*(d:ℝ)*K)*L^2*ε+
        (2*D*U^2)*L^3*ε+(C*(d:ℝ)*K)*L*t+(C*(d:ℝ)*K)*L*ε+(D*U)*L^2*ε+D*L*ε:=by
      dsimp only[U]
      ring
    _≤K*L^2*t+K*L^3*ε+(4*U*C*(d:ℝ)*K)*L^2*t+(4*U*C*(d:ℝ)*K)*L^3*ε+
        (2*D*U^2)*L^3*ε+(C*(d:ℝ)*K)*L^2*t+(C*(d:ℝ)*K)*L^3*ε+(D*U)*L^3*ε+D*L^3*ε:=by
      gcongr
    _=(K+4*U*C*(d:ℝ)*K+C*(d:ℝ)*K)*L^2*t+
        (K+4*U*C*(d:ℝ)*K+C*(d:ℝ)*K+2*D*U^2+D*U+D)*L^3*ε:=by ring
    _≤_:=by
      unfold smallSampleKernelCoefficient
      change _≤(K+4*U*C*(d:ℝ)*K+C*(d:ℝ)*K+2*D*U^2+D*U+D+1)*L^2*t+
        (K+4*U*C*(d:ℝ)*K+C*(d:ℝ)*K+2*D*U^2+D*U+D+1)*L^3*ε
      have hrest:0≤2*D*U^2+D*U+D:=by positivity
      have hleft:K+4*U*C*(d:ℝ)*K+C*(d:ℝ)*K≤
          K+4*U*C*(d:ℝ)*K+C*(d:ℝ)*K+2*D*U^2+D*U+D+1:=by linarith
      have hright:K+4*U*C*(d:ℝ)*K+C*(d:ℝ)*K+2*D*U^2+D*U+D≤
          K+4*U*C*(d:ℝ)*K+C*(d:ℝ)*K+2*D*U^2+D*U+D+1:=by linarith
      exact add_le_add (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hleft (sq_nonneg L)) ht)
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hright (pow_nonneg hL0 3)) hε)

namespace DeficientGraph
variable {V:Type}[Fintype V][DecidableEq V]{d:ℕ}

theorem small_sample_entire_kernel_decay (g:DeficientGraph V d)(hd:3≤d)(T:Set V)
    (q z:ℂ)(hz:0<z.im)(hq:0≤q.im)(K L ε C D:ℝ)
    (hK:0≤K)(hL:1≤L)(hε:0≤ε)(hεone:ε≤1)(hC:0≤C)(hD:0≤D)
    (hT:Nat.card T≤2)(hcore:g.LeafCoreDecayBound T q z K L ε)
    (hB:∀b:T,∑c:T,‖g.extensionGreen q z b.val c.val‖≤C)
    (hoff:∀b c:T,b≠c→‖g.extensionGreen q z b.val c.val‖≤D*L*ε)
    (x y:V)(h:ℕ)(hfar:((2*h+2:ℕ):ℕ∞)≤g.graph.edist x y) :
    ‖g.extensionGreen q z x y‖≤smallSampleKernelCoefficient d K C D*L^2*physicalTransfer d z^h+
      smallSampleKernelCoefficient d K C D*L^3*ε := by
  have hL0:0≤L:=by linarith
  have hδ:0≤D*L*ε:=by positivity
  have hraw:=g.small_sample_entire_kernel_raw hd T q z hz hq K L ε C (D*L*ε)
    hK hL0 hε hεone hC hδ hT hcore hB hoff x y h hfar
  dsimp only at hraw
  let F:=K*L*physicalTransfer d z^h+K*L*ε
  let a:=4*(d:ℝ)*K*L
  have ht:0≤physicalTransfer d z^h:=pow_nonneg (physicalTransfer_pos d hd z).le h
  have hF:0≤F:=by dsimp only[F];positivity
  have ha:0≤a:=by dsimp only[a];positivity
  have hdR:(3:ℝ)≤d:=Nat.cast_le.mpr hd
  have hsqrt:1≤Real.sqrt ((d:ℝ)-1):=by
    have he:=Real.sq_sqrt (show 0≤(d:ℝ)-1 by linarith)
    nlinarith[Real.sqrt_nonneg ((d:ℝ)-1)]
  have hratio:(d:ℝ)/Real.sqrt ((d:ℝ)-1)≤d:=by
    apply (div_le_iff₀ (by linarith:0<Real.sqrt ((d:ℝ)-1))).mpr
    nlinarith [Nat.cast_nonneg (α:=ℝ) d]
  have hmon:F+2*((F*((d:ℝ)/Real.sqrt ((d:ℝ)-1)))*(a*C)+
        a*(C*(F*((d:ℝ)/Real.sqrt ((d:ℝ)-1)))+(D*L*ε)*a))+
        (C*(F*((d:ℝ)/Real.sqrt ((d:ℝ)-1)))+(D*L*ε)*a)+D*L*ε≤
      F+2*((F*(d:ℝ))*(a*C)+a*(C*(F*(d:ℝ))+(D*L*ε)*a))+
        (C*(F*(d:ℝ))+(D*L*ε)*a)+D*L*ε:=by
    gcongr
  exact hraw.trans (hmon.trans (smallSample_polynomial_bound d K C D L ε
    (physicalTransfer d z^h) hK hC hD hL hε ht))

end DeficientGraph
end LocalLaw
