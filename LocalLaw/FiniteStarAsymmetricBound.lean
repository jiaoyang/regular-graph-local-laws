import LocalLaw.FiniteStarComparison
import LocalLaw.WeightedAsymmetricCoreL1

/-! # Quantitative finite-star lifting with the true harmonic L1 weights

The uniform core error pays the two actual harmonic L1 norms. Only the
localization tail pays the fixed finite-star index count.
-/

open scoped BigOperators
namespace LocalLaw
variable {I J:Type} [Fintype I] [Fintype J]

omit [Fintype J] in
theorem finite_star_asymmetric_error (GM GN:Matrix (I⊕J) (I⊕J) ℂ)
    (R P:Matrix I I ℂ) [DecidableEq I]
    (hlift:GM-GN=(GM.submatrix id Sum.inl*R⁻¹)*(R-P)*(P⁻¹*GN.submatrix Sum.inl id))
    (x y:I⊕J)(ρ K s δ v C A B:ℝ)
    (hρ:0≤ρ)(hρone:ρ≤1)(hK:0≤K)(hs:0≤s)(hδ:0≤δ)(hv:0≤v)(hC:0≤C)(hA:0≤A)(hB:0≤B)
    (r:ℕ)(ri di dj:I→ℕ)(hri:∀i,r≤ri i+di i)(hrj:∀j,r≤ri j+dj j)
    (ha:∀i,‖(GM.submatrix id Sum.inl*R⁻¹) x i‖≤K*ρ^(di i)+s)
    (hb:∀j,‖(P⁻¹*GN.submatrix Sum.inl id) j y‖≤K*ρ^(dj j)+s)
    (he:∀i j,‖(R-P) i j‖≤δ+v*ρ^(ri i+ri j))(hecap:∀i j,‖(R-P) i j‖≤C)
    (hleft:(∑i,‖(GM.submatrix id Sum.inl*R⁻¹) x i‖)≤A)
    (hright:(∑j,‖(P⁻¹*GN.submatrix Sum.inl id) j y‖)≤B) :
    ‖GM x y-GN x y‖≤δ*A*B+(Fintype.card I:ℝ)^2*K^2*v*ρ^(2*r)+
      C*s*(Fintype.card I:ℝ)*(A+B) := by
  have hh:=weighted_asymmetric_core_sum_l1
    (fun i=>(GM.submatrix id Sum.inl*R⁻¹) x i)
    (fun j=>(P⁻¹*GN.submatrix Sum.inl id) j y) (R-P) ρ K s δ v C A B
    hρ hρone hK hs hδ hv hC hA hB r ri di dj hri hrj ha hb he hecap hleft hright
  have heq:GM x y-GN x y=∑i,∑j,
      (GM.submatrix id Sum.inl*R⁻¹) x i*(R-P) i j*(P⁻¹*GN.submatrix Sum.inl id) j y := by
    change (GM-GN) x y=_
    rw [hlift]
    simp only [Matrix.mul_apply,Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [heq]
  exact hh

end LocalLaw
