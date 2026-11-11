import SpectralConsequences.OutsideEdgeMeans
import SpectralConsequences.FiniteMeanAlgebra

/-! # Exact one- and two-coordinate means under uniform independent draws

Finite function-space equivalences supply independence. No product-law
or expected-value factorization is assumed as a probabilistic premise.
-/
open scoped BigOperators
noncomputable section
namespace SpectralConsequences
open LocalLaw
variable {E F I:Type*} [Fintype E] [Fintype F] [Fintype I]

theorem finiteComplexMean_const [Nonempty E] (c:ℂ) :
    finiteComplexMean (fun _e:E=>c)=c := by
  unfold finiteComplexMean
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Complex.real_smul,
    Complex.ofReal_inv,Complex.ofReal_natCast]
  have hn:(Fintype.card E:ℂ)≠0:=by exact_mod_cast ne_of_gt Fintype.card_pos
  rw [←mul_assoc,inv_mul_cancel₀ hn,one_mul]

theorem finiteComplexMean_prod (f:E×F→ℂ) :
    finiteComplexMean f=finiteComplexMean (fun e:E=>finiteComplexMean (fun t:F=>f (e,t))) := by
  unfold finiteComplexMean
  rw [Fintype.card_prod,Fintype.sum_prod_type]
  simp only [Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_natCast,
    Nat.cast_mul,mul_inv_rev,Complex.ofReal_mul,Complex.ofReal_inv,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro t _
  ring

/-- Every fixed coordinate of the actual uniform function draw is uniform. -/
theorem uniform_function_coordinate_mean [DecidableEq I] [Nonempty E] (i:I) (f:E→ℂ) :
    finiteComplexMean (fun s:I→E=>f (s i))=finiteComplexMean f := by
  classical
  have h:=finiteComplexMean_equiv (Equiv.funSplitAt i E)
    (fun u:E×({j:I//j≠i}→E)=>f u.1)
  change finiteComplexMean (fun s:I→E=>f (s i)) = _ at h
  rw [finiteComplexMean_prod] at h
  simp_rw [finiteComplexMean_const] at h
  exact h

/-- Distinct fixed coordinates are exactly two independent uniform draws. -/
theorem uniform_function_two_coordinate_mean [DecidableEq I] [Nonempty E] (i j:I) (hij:i≠j)
    (f:E→E→ℂ) :
    finiteComplexMean (fun s:I→E=>f (s i) (s j))=
      finiteComplexMean (fun a:E=>finiteComplexMean (f a)) := by
  classical
  have hji:j≠i:=Ne.symm hij
  have h:=finiteComplexMean_equiv (Equiv.funSplitAt i E)
    (fun u:E×({k:I//k≠i}→E)=>f u.1 (u.2 ⟨j,hji⟩))
  change finiteComplexMean (fun s:I→E=>f (s i) (s j)) = _ at h
  rw [finiteComplexMean_prod] at h
  simp_rw [uniform_function_coordinate_mean] at h
  exact h

end SpectralConsequences
