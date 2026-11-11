import LocalLaw.AsymmetricSchurProducts

/-! # Weighted diagonal-Schur comparison with asymmetric localization tails -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
variable {I:Type} [Fintype I] [DecidableEq I]

theorem asymmetric_diagonal_schur_target_bound (x y p:ℂ) (a b a' b':I→ℂ) (R S:Matrix I I ℂ)
    (δ σ ρ u v C A B A' B':ℝ)
    (hσ:0≤σ) (hρ:0≤ρ) (hρone:ρ≤1) (hu:0≤u) (hv:0≤v) (hC:0≤C)
    (hA:0≤A) (hB:0≤B) (hA':0≤A') (hB':0≤B') (hxy:‖x-y‖≤δ)
    (ha:(∑i,‖a i‖)≤A) (hb:(∑i,‖b i‖)≤B) (ha':(∑i,‖a' i‖)≤A') (hb':(∑i,‖b' i‖)≤B')
    (hR:∀i j,‖R⁻¹ i j-(if i=j then p⁻¹ else 0)‖≤σ)
    (hS:∀i j,‖S⁻¹ i j-(if i=j then p⁻¹ else 0)‖≤σ)
    (N:ℕ) (m di dj:I→ℕ) (hm:∀i,m i≤N) (hmi:∀i,m i≤di i) (hmj:∀i,m i≤dj i)
    (hea:∀i,‖a i-a' i‖≤u+v*ρ^(N-m i)) (heb:∀i,‖b i-b' i‖≤u+v*ρ^(N-m i))
    (hadecay:∀i,‖a' i‖≤C*ρ^(di i)) (hbdecay:∀i,‖b i‖≤C*ρ^(dj i)) :
    ‖(x-schurBilinear a R⁻¹ b)-(y-schurBilinear a' S⁻¹ b')‖≤
      δ+‖p⁻¹‖*(u*(B+A')+2*v*C*(Fintype.card I:ℝ)*ρ^N)+σ*(A*B+A'*B') := by
  have hs:=two_diagonal_schur_target_bound x y p a b a' b' R S δ σ A B A' B'
    hσ hA hB hA' hB' hxy ha hb ha' hb' hR hS
  have hp:=asymmetric_schur_products_bound a b a' b' ρ u v C B A' hρ hρone hu hv hC
    N m di dj hm hmi hmj hea heb hadecay hbdecay hb ha'
  exact hs.trans (add_le_add_right (add_le_add_left
    (mul_le_mul_of_nonneg_left hp (norm_nonneg _)) _) _)

end LocalLaw
