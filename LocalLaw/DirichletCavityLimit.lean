import LocalLaw.Semicircle
import LocalLaw.RegularTree
import LocalLaw.RadialCavityRecursion

/-! # Genuine Dirichlet finite-tree exhaustion selects the physical root

The boundary value zero is the ordinary Dirichlet truncation. Its true finite
tree resolvent converges to the physical semicircle root; no limiting-value
or infinite-resolvent premise is used.
-/

open Filter
open scoped Topology
noncomputable section
namespace LocalLaw

theorem one_sub_pow_ne_zero_of_norm_lt_one {m : ℂ} (hm : ‖m‖<1) (k : ℕ) (hk : 0<k) :
    1-m^k≠0 := by
  have hp : ‖m^k‖<1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hm (Nat.ne_zero_of_lt hk)
  intro hz
  have heq : m^k=1 := (sub_eq_zero.mp hz).symm
  rw [heq,norm_one] at hp
  exact (lt_irrefl _ hp)

theorem dirichlet_cavity_denominator_identity (m : ℂ) (n : ℕ) :
    (1-m^2)*cavityDenominator m (0-m) n=1-m^(2*n+2) := by
  have h := cavitySum_geometric m n
  dsimp only [cavityDenominator]
  rw [pow_add]
  linear_combination m^2*h

theorem dirichlet_cavity_closed_form {m z : ℂ} (hm : m^2+z*m+1=0) (hmnorm : ‖m‖<1) (n : ℕ) :
    cavityIterate z 0 n=m*(1-m^(2*n))/(1-m^(2*n+2)) := by
  have hD (j : ℕ) : cavityDenominator m (0-m) j≠0 := by
    intro hzero
    have hh := dirichlet_cavity_denominator_identity m j
    rw [hzero,mul_zero] at hh
    exact one_sub_pow_ne_zero_of_norm_lt_one hmnorm (2*j+2) (by omega) hh.symm
  have hbase : 1-m^2≠0 := one_sub_pow_ne_zero_of_norm_lt_one hmnorm 2 (by omega)
  have hpower : 1-m^(2*n+2)≠0 := one_sub_pow_ne_zero_of_norm_lt_one hmnorm _ (by omega)
  have hden : cavityDenominator m (0-m) n=(1-m^(2*n+2))/(1-m^2) := by
    apply (eq_div_iff hbase).mpr
    simpa only [mul_comm] using dirichlet_cavity_denominator_identity m n
  rw [cavity_iterate_exact hm n (fun j _ => hD j),hden]
  field_simp
  rw [pow_add]
  ring

theorem cavityIterate_zero_tendsto_physical (z : ℂ) (hz : 0<z.im) :
    Tendsto (fun n : ℕ => cavityIterate z 0 n) atTop (𝓝 (semicircleRoot z)) := by
  let m := semicircleRoot z
  have hmnorm : ‖m‖<1 := semicircleRoot_norm_lt_one hz
  have hp : Tendsto (fun n : ℕ => (m^2)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg _) hmnorm (by norm_num))
  have hnum : Tendsto (fun n : ℕ => m*(1-(m^2)^n)) atTop (𝓝 m) := by
    simpa only [sub_zero,mul_one] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => m) atTop (𝓝 m)).mul
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℂ)) atTop (𝓝 1)).sub hp)
  have hden : Tendsto (fun n : ℕ => 1-(m^2)^n*m^2) atTop (𝓝 1) := by
    simpa only [zero_mul,sub_zero] using tendsto_const_nhds.sub (hp.mul_const (m^2))
  have hquot := hnum.div hden (by norm_num : (1:ℂ)≠0)
  have hquot' : Tendsto (fun n : ℕ => m*(1-m^(2*n))/(1-m^(2*n+2))) atTop (𝓝 m) := by
    simpa only [div_one,←pow_mul,←pow_add] using hquot
  exact hquot'.congr' (Filter.Eventually.of_forall (fun n =>
    (dirichlet_cavity_closed_form (semicircleRoot_equation z) hmnorm n).symm))

/-- Every finite cavity-tree matrix is nonsingular with ordinary zero
boundary, and its actual inverse root entry converges to the physical root. -/
theorem dirichlet_cavityTree_inverse_root (k : ℕ) (hk : 0<k) (z : ℂ) (hz : 0<z.im) (n : ℕ) :
    IsUnit (cavityTreeMatrix k (normalizedCavityEdge k) z 0 n) ∧
      (cavityTreeMatrix k (normalizedCavityEdge k) z 0 n)⁻¹ (cavityTreeRoot k n) (cavityTreeRoot k n)=
        cavityIterate z 0 (n+1) :=
  cavityTree_inverse_root k _ z 0 (normalizedCavityEdge_normalization k hk) n
    (fun j _ => cavityIterate_step_nonzero z 0 hz (by norm_num) j)

theorem dirichlet_cavityTree_root_tendsto (k : ℕ) (hk : 0<k) (z : ℂ) (hz : 0<z.im) :
    Tendsto (fun n : ℕ => (cavityTreeMatrix k (normalizedCavityEdge k) z 0 n)⁻¹
      (cavityTreeRoot k n) (cavityTreeRoot k n)) atTop (𝓝 (semicircleRoot z)) := by
  have h := (cavityIterate_zero_tendsto_physical z hz).comp (tendsto_add_atTop_nat 1)
  exact h.congr' (Filter.Eventually.of_forall (fun n => (dirichlet_cavityTree_inverse_root k hk z hz n).2.symm))

end LocalLaw
