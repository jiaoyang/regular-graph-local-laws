import SpectralConsequences.FiniteMomentBootstrap
import SpectralConsequences.FiniteMomentIdentity

/-! # Solving the fluctuation-averaging moment recurrence

The square-root scale is derived from the moment recurrence. The variance
increment A must be no larger than epsilon; this is the source parameter
comparison used after equation (7.13).
-/
open scoped BigOperators
noncomputable section
namespace SpectralConsequences

/-- The drift occupies degree one; symmetric increment terms start at degree
two. The finite index j represents the drop j+1 in the moment order. -/
def fluctuationMomentCoefficient {n : ℕ} (B D ε A : ℝ) (j : Fin n) : ℝ :=
  if j.val=0 then B else D*ε*A^j.val

theorem fluctuation_increment_power_bound (ε A : ℝ) (hε : 0 ≤ ε)
    (hA : 0 ≤ A) (hAε : A ≤ ε) (j : ℕ) (hj : 1 ≤ j) :
    ε*A^j ≤ (Real.sqrt (ε*A))^(j+1) := by
  let S := Real.sqrt (ε*A)
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hSsq : S^2 = ε*A := Real.sq_sqrt (mul_nonneg hε hA)
  have hAS : A ≤ S := by nlinarith
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j≠0)
  rw [hk,pow_succ]
  calc
    ε*(A^k*A) = S^2*A^k := by rw [hSsq];ring
    _ ≤ S^2*S^k := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hA hAS k) (sq_nonneg S)
    _ = S^(k+1+1) := by rw [←pow_add];congr 1;omega

theorem fluctuation_moment_coefficient_budget (n : ℕ) (B D ε A K : ℝ)
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hε : 0 ≤ ε) (hA : 0 ≤ A) (hAε : A ≤ ε)
    (hK : 1 ≤ K) (hKB : 4*(n:ℝ) ≤ K) (hKD : 4*(n:ℝ)*D ≤ K)
    (j : Fin n) :
    4*(n:ℝ)*fluctuationMomentCoefficient B D ε A j ≤
      (K*(B+Real.sqrt (ε*A)))^(j.val+1) := by
  let S := Real.sqrt (ε*A)
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hK0 : 0 ≤ K := by linarith
  by_cases hj : j.val=0
  · simp only [fluctuationMomentCoefficient,hj,if_true,zero_add,pow_one]
    nlinarith [mul_nonneg hK0 hS]
  · have hpower := fluctuation_increment_power_bound ε A hε hA hAε j.val (by omega)
    have hscale : 4*(n:ℝ)*(D*ε*A^j.val) ≤ K*S^(j.val+1) := by
      calc
        _ = (4*(n:ℝ)*D)*(ε*A^j.val) := by ring
        _ ≤ (4*(n:ℝ)*D)*S^(j.val+1) :=
          mul_le_mul_of_nonneg_left hpower (by positivity)
        _ ≤ K*S^(j.val+1) := mul_le_mul_of_nonneg_right hKD (pow_nonneg hS _)
    have hKpow : K ≤ K^(j.val+1) := by
      rw [pow_succ]
      have hh : 1 ≤ K^j.val := one_le_pow₀ hK
      nlinarith
    have hSpow : S^(j.val+1) ≤ (B+S)^(j.val+1) :=
      pow_le_pow_left₀ hS (by linarith) _
    simp only [fluctuationMomentCoefficient,hj,if_false]
    apply hscale.trans
    rw [mul_pow]
    exact mul_le_mul hKpow hSpow (pow_nonneg hS _) (pow_nonneg hK0 _)

/-- The actual recurrence implies the fluctuation-averaging scale. Its input
contains lower moments, not the desired high-moment bound. -/
theorem fluctuation_moment_recurrence_bound {Ω : Type*} [Fintype Ω]
    (w f : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (hf : ∀ ω, 0 ≤ f ω)
    (hwtotal : ∑ ω, w ω ≤ 1) (n : ℕ) (hn : 0 < n)
    (B D ε A K : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hε : 0 ≤ ε) (hA : 0 ≤ A) (hAε : A ≤ ε)
    (hK : 1 ≤ K) (hKB : 4*(n:ℝ) ≤ K) (hKD : 4*(n:ℝ)*D ≤ K)
    (hrecurrence : (∑ ω, w ω*f ω^n) ≤
      ∑ j : Fin n, fluctuationMomentCoefficient B D ε A j*
        (∑ ω, w ω*f ω^(n-(j.val+1)))) :
    (∑ ω, w ω*f ω^n) ≤ (K*(B+Real.sqrt (ε*A)))^n := by
  apply finite_moment_recurrence_bound w f hw hf hwtotal n hn
    (fluctuationMomentCoefficient B D ε A) (K*(B+Real.sqrt (ε*A))) (by positivity)
  · intro j
    exact fluctuation_moment_coefficient_budget n B D ε A K hB hD hε hA hAε hK hKB hKD j
  · exact hrecurrence

/-- Markov's inequality for the actual complex residual on its regularity
event, with strict threshold and arbitrary finite nonnegative weights. -/
theorem truncated_moment_markov {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (A : Ω → Prop) [DecidablePred A]
    (F : Ω → ℂ) (p : ℕ) (t : ℝ) (ht : 0 < t) :
    LocalLaw.eventMass w (fun ω => A ω ∧ t < ‖F ω‖)*t^(2*p) ≤
      truncatedMoment w A F p := by
  classical
  unfold LocalLaw.eventMass truncatedMoment
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro ω _
  by_cases hA : A ω
  · by_cases hF : t < ‖F ω‖
    · simp only [hA,hF,and_self,if_true]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht.le hF.le _) (hw ω)
    · simp only [hA,hF,and_false,if_false,if_true,zero_mul]
      exact mul_nonneg (hw ω) (pow_nonneg (norm_nonneg _) _)
  · simp only [hA,false_and,if_false,zero_mul]
    exact le_rfl

end SpectralConsequences
