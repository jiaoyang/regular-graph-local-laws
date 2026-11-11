import LocalLaw.BoundaryDefectAggregation

/-!
# Polynomial-log budgets for the sparse surgery defect

Quadratic-log many bad labels and the coarser good off-diagonal estimate
O(delta^2+n*phi*delta+phi) give the genuine log^5(N)*epsilon column budget.
-/

namespace LocalLaw

def sparseBoundaryColumnConstant (U V D G : ℝ) : ℝ :=
  (V+1)*D+G*(U*D^2+U^2*D+U)

theorem sparse_boundary_source_column_budget (a : ℕ) (L ε n B δ φ γ U V D G : ℝ)
    (ha : 1 ≤ a) (hL : 1 ≤ L) (hε : 0 ≤ ε)
    (hn : 0 ≤ n) (_hB : 0 ≤ B) (hδ : 0 ≤ δ) (hφ : 0 ≤ φ) (_hγ : 0 ≤ γ)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hD : 0 ≤ D) (hG : 0 ≤ G)
    (hcap : ε*L^(4*a) ≤ 1) (hcount : n ≤ U*L^(2*a))
    (hbad : B ≤ V*L^2) (herror : δ ≤ D*L^3*ε)
    (hcorrelation : φ*L^(4*a) ≤ ε) (hgood : γ ≤ G*(δ^2+n*φ*δ+φ)) :
    (B+1)*δ+n*γ ≤ sparseBoundaryColumnConstant U V D G * L^5 * ε := by
  have hL0 : 0 ≤ L := by linarith
  have hL2 : 1 ≤ L^2 := one_le_pow₀ hL
  have hL5 : 1 ≤ L^5 := one_le_pow₀ hL
  have heps : ε*L^(2*a+1) ≤ 1 :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (by omega)) hε).trans hcap
  have hphi : φ*L^(2*a) ≤ ε :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (by omega)) hφ).trans hcorrelation
  have hnphi : n*φ ≤ U*ε := by
    calc
      _ ≤ (U*L^(2*a))*φ := mul_le_mul_of_nonneg_right hcount hφ
      _ = U*(φ*L^(2*a)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hphi hU
  have hndelta : n*δ ≤ U*D*L^2 := by
    calc
      _ ≤ (U*L^(2*a))*(D*L^3*ε) := mul_le_mul hcount herror hδ (by positivity)
      _ = U*D*(ε*L^(2*a+1))*L^2 := by
        rw [pow_succ L (2*a)]
        norm_num [pow_succ]
        ring
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left heps (by positivity : 0 ≤ U*D*L^2)]
  have hfirst : n*δ^2 ≤ U*D^2*L^5*ε := by
    calc
      _ = (n*δ)*δ := by ring
      _ ≤ (U*D*L^2)*(D*L^3*ε) := mul_le_mul hndelta herror hδ (by positivity)
      _ = _ := by norm_num [pow_succ]; ring
  have hsecond : n*(n*φ*δ) ≤ U^2*D*L^5*ε := by
    calc
      _ = (n*φ)*(n*δ) := by ring
      _ ≤ (U*ε)*(U*D*L^2) := mul_le_mul hnphi hndelta (by positivity) (by positivity)
      _ = U^2*D*ε*L^2 := by ring
      _ ≤ U^2*D*ε*L^5 := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hL (by omega)) (by positivity)
      _ = _ := by ring
  have hthird : n*φ ≤ U*L^5*ε :=
    hnphi.trans (by nlinarith [mul_le_mul_of_nonneg_left hL5 (mul_nonneg hU hε)])
  have hbadone : B+1 ≤ (V+1)*L^2 := by nlinarith only [hbad,hL2]
  have hbadterm : (B+1)*δ ≤ (V+1)*D*L^5*ε := by
    apply (mul_le_mul hbadone herror hδ (by positivity)).trans_eq
    norm_num [pow_succ]; ring
  have hgoodterm := mul_le_mul_of_nonneg_left hgood hn
  have hsum : n*γ ≤ G*(U*D^2+U^2*D+U)*L^5*ε := by
    nlinarith only [hgoodterm,mul_le_mul_of_nonneg_left hfirst hG,
      mul_le_mul_of_nonneg_left hsecond hG,mul_le_mul_of_nonneg_left hthird hG]
  dsimp only [sparseBoundaryColumnConstant]
  nlinarith only [hbadterm,hsum]

end LocalLaw
