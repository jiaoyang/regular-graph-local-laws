import SpectralConsequences.FiniteMomentIdentity
import SpectralConsequences.BoundaryMeanAggregation
import SpectralConsequences.ComplexMomentAlgebra

/-! # Averaging local observables in the genuine complex moment identity -/
open scoped BigOperators
noncomputable section
namespace SpectralConsequences
open LocalLaw
variable {X I:Type*} [Fintype X] [Fintype I]

theorem finiteExpectation_mean_sites (w:X→ℝ) (f:I→X→ℂ):
    finiteExpectation w (fun x=>finiteComplexMean (fun i=>f i x))=
      finiteComplexMean (fun i=>finiteExpectation w (f i)):=by
  unfold finiteExpectation finiteComplexMean
  simp only [Complex.real_smul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem truncated_moment_site_energy (w:X→ℝ) (A:X→Prop) [DecidablePred A]
    (χ:I→X→Prop) [∀i,DecidablePred (χ i)] (h:I→X→ℂ) (target F error:X→ℂ)
    (p:ℕ) (hp:1≤p)
    (hmean:∀x,A x→F x=finiteComplexMean (fun i=>if χ i x then h i x-target x else 0)+error x):
    (truncatedMoment w A F p:ℂ)=
      finiteComplexMean (fun i=>finiteExpectation w (fun x=>
        if A x ∧ χ i x then (h i x-target x)*complexMomentTest p (F x) else 0))+
      finiteExpectation w (fun x=>if A x then error x*complexMomentTest p (F x) else 0):=by
  classical
  have he: (truncatedMoment w A F p:ℂ)=
      finiteExpectation w (fun x=>if A x then F x*complexMomentTest p (F x) else 0):=by
    simp only [truncatedMoment,finiteExpectation,Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx:A x <;>simp only [hx,if_true,if_false,mul_zero,
      complexMomentTest_energy p hp,Complex.ofReal_mul,Complex.ofReal_zero]
  rw [he]
  have hpoint (x:X):(if A x then F x*complexMomentTest p (F x) else 0)=
      finiteComplexMean (fun i=>if A x ∧ χ i x then (h i x-target x)*complexMomentTest p (F x) else 0)+
      (if A x then error x*complexMomentTest p (F x) else 0):=by
    by_cases hx:A x
    · rw [if_pos hx,hmean x hx,add_mul,if_pos hx]
      congr 1
      unfold finiteComplexMean
      simp only [Complex.real_smul,Finset.sum_mul,mul_assoc]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi:χ i x <;>simp [hx,hi]
    · simp only [hx,if_false,false_and,zero_add,finiteComplexMean]
      simp
  simp_rw [hpoint]
  rw [finiteExpectation_add,finiteExpectation_mean_sites]

theorem truncated_moment_error_term (w:X→ℝ) (hw:∀x,0≤w x)
    (A:X→Prop) [DecidablePred A] (F error:X→ℂ) (p:ℕ) (C:ℝ)
    (herr:∀x,A x→‖error x‖≤C):
    ‖finiteExpectation w (fun x=>if A x then error x*complexMomentTest p (F x) else 0)‖≤
      C*(∑x,if A x then w x*‖F x‖^(2*p-1) else 0):=by
  apply (finiteExpectation_norm_le w hw _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx:A x
  · simp only [hx,if_true,norm_mul,complexMomentTest_norm]
    have hh:=mul_le_mul_of_nonneg_right (herr x hx) (pow_nonneg (norm_nonneg (F x)) (2*p-1))
    exact (mul_le_mul_of_nonneg_left hh (hw x)).trans_eq (by ring)
  · simp [hx]

end SpectralConsequences
