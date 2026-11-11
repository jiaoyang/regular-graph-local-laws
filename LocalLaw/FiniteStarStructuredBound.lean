import LocalLaw.FiniteStarAsymmetricBound

/-! # Structured finite-star error with fixed harmonic row mass -/
open scoped BigOperators
namespace LocalLaw
variable {I J:Type}[Fintype I][Fintype J][DecidableEq I]

omit [Fintype J] in
theorem finite_star_structured_bound (GM GN:Matrix (I⊕J) (I⊕J) ℂ)(R P:Matrix I I ℂ)
    (hlift:GM-GN=(GM.submatrix id Sum.inl*R⁻¹)*(R-P)*(P⁻¹*GN.submatrix Sum.inl id))
    (x y:I⊕J)(ρ KM K D C H V μ m L ε:ℝ)
    (hρ:0≤ρ)(hρone:ρ≤1)(hKM:0≤KM)(hK:0≤K)(hD:0≤D)(hC:0≤C)(hH:0≤H)(hV:0≤V)
    (hμ:0≤μ)(_hm:0≤ m)(hL:0≤L)(hε:0≤ε)(hcard:(Fintype.card I:ℝ)≤ m)
    (r:ℕ)(ri di dj:I→ℕ)(hri:∀i,r≤ri i+di i)(hrj:∀j,r≤ri j+dj j)
    (ha:∀i,‖(GM.submatrix id Sum.inl*R⁻¹) x i‖≤(K*L)*ρ^(di i)+D*L*ε)
    (hb:∀j,‖(P⁻¹*GN.submatrix Sum.inl id) j y‖≤(K*L)*ρ^(dj j)+D*L*ε)
    (he:∀i j,‖(R-P) i j‖≤KM*L*ε+(V*(μ+1)*L^2)*ρ^(ri i+ri j))
    (hecap:∀i j,‖(R-P) i j‖≤C)
    (hleft:(∑i,‖(GM.submatrix id Sum.inl*R⁻¹) x i‖)≤H)
    (hright:(∑j,‖(P⁻¹*GN.submatrix Sum.inl id) j y‖)≤H):
    ‖GM x y-GN x y‖≤(KM*H^2+2*C*D*m*H)*L*ε+
      (m^2*K^2*V)*(μ+1)*L^4*ρ^(2*r):=by
  have hh:=finite_star_asymmetric_error GM GN R P hlift x y ρ (K*L) (D*L*ε)
    (KM*L*ε) (V*(μ+1)*L^2) C H H hρ hρone (by positivity) (by positivity)
    (by positivity) (by positivity) hC hH hH r ri di dj hri hrj ha hb he hecap hleft hright
  have hcard2:(Fintype.card I:ℝ)^2≤ m^2:=pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2
  have htail:(Fintype.card I:ℝ)^2*(K*L)^2*(V*(μ+1)*L^2)*ρ^(2*r)≤
      m^2*(K*L)^2*(V*(μ+1)*L^2)*ρ^(2*r):=by gcongr
  have hres:C*(D*L*ε)*(Fintype.card I:ℝ)*(H+H)≤C*(D*L*ε)*m*(H+H):=by gcongr
  exact hh.trans (((add_le_add (add_le_add_left htail _) hres)).trans_eq (by ring))

end LocalLaw
