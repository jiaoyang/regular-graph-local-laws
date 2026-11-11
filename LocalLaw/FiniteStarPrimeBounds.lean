import LocalLaw.FiniteStarAsymmetricBound

/-! # Quantitative prime-error assembly with the actual finite star count -/

open scoped BigOperators
namespace LocalLaw
variable {I J:Type} [Fintype I] [Fintype J] [DecidableEq I]

omit [Fintype J] in
theorem finite_star_prime_bound (GM GN:Matrix (I⊕J) (I⊕J) ℂ)(R P:Matrix I I ℂ)
    (hlift:GM-GN=(GM.submatrix id Sum.inl*R⁻¹)*(R-P)*(P⁻¹*GN.submatrix Sum.inl id))
    (x y:I⊕J)(ρ KM K D C H V n m L ε Dfinal:ℝ)
    (hρ:0≤ρ)(hρone:ρ≤1)(hKM:0≤KM)(hK:0≤K)(hD:0≤D)(hC:0≤C)(hH:0≤H)(hV:0≤V)
    (hn:0≤n)(_hm:0 ≤ m)(hL:1≤L)(hε:0≤ε)(hcard:(Fintype.card I:ℝ)≤ m)
    (r:ℕ)(ri di dj:I→ℕ)(hri:∀i,r≤ri i+di i)(hrj:∀j,r≤ri j+dj j)
    (ha:∀i,‖(GM.submatrix id Sum.inl*R⁻¹) x i‖≤(K*L)*ρ^(di i)+D*L^2*ε)
    (hb:∀j,‖(P⁻¹*GN.submatrix Sum.inl id) j y‖≤(K*L)*ρ^(dj j)+D*L^2*ε)
    (he:∀i j,‖(R-P) i j‖≤(KM*L*ε)+(V*(n+1)*L^2)*ρ^(ri i+ri j))
    (hecap:∀i j,‖(R-P) i j‖≤C)
    (hleft:(∑i,‖(GM.submatrix id Sum.inl*R⁻¹) x i‖)≤H*L)
    (hright:(∑j,‖(P⁻¹*GN.submatrix Sum.inl id) j y‖)≤H*L)
    (hrate:(KM*L*ε)*(H*L)*(H*L)+m^2*(K*L)^2*(V*(n+1)*L^2)*ρ^(2*r)+
      C*(D*L^2*ε)*m*(H*L+H*L)≤Dfinal*(L^3*ε)) :
    ‖GM x y-GN x y‖≤Dfinal*(L^3*ε) := by
  have hL0:0≤L:=by linarith
  have hv:0≤V*(n+1)*L^2:=by positivity
  have hh:=finite_star_asymmetric_error GM GN R P hlift x y ρ (K*L) (D*L^2*ε)
    (KM*L*ε) (V*(n+1)*L^2) C (H*L) (H*L)
    hρ hρone (by positivity) (by positivity) (by positivity) hv hC (by positivity) (by positivity)
    r ri di dj hri hrj ha hb he hecap hleft hright
  have hcard2:(Fintype.card I:ℝ)^2≤ m^2:=pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2
  have htail:(Fintype.card I:ℝ)^2*(K*L)^2*(V*(n+1)*L^2)*ρ^(2*r)≤
      m^2*(K*L)^2*(V*(n+1)*L^2)*ρ^(2*r):=by gcongr
  have hres:C*(D*L^2*ε)*(Fintype.card I:ℝ)*(H*L+H*L)≤C*(D*L^2*ε)*m*(H*L+H*L):=by gcongr
  exact hh.trans ((add_le_add (add_le_add_left htail _) hres).trans hrate)

end LocalLaw
