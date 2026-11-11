import SpectralConsequences.FiniteMomentBootstrap

/-! # Absorbing drift, variance and exceptional-event contributions

The recurrence is between genuine lower moments. The final high-moment
estimate follows by two elementary mixed-power absorptions.
-/
open scoped BigOperators
noncomputable section
namespace SpectralConsequences

theorem finite_three_term_moment_bound {X:Type*} [Fintype X]
    (w f:X→ℝ) (hw:∀x,0≤w x) (hf:∀x,0≤f x) (hmass:∑x,w x≤1)
    (n:ℕ) (hn:2≤n) (B C D E T:ℝ) (hT:0≤T)
    (hB:8*B≤T) (hC:8*C≤T^2) (hD:8*D≤T^n) (hE:8*E≤T^n)
    (hrec:(∑x,w x*f x^n)≤
      B*(∑x,w x*f x^(n-1))+C*(∑x,w x*f x^(n-2))+D+E):
    (∑x,w x*f x^n)≤T^n:=by
  let M:=∑x,w x*f x^n
  have hM:0≤M:=Finset.sum_nonneg (fun x _=>mul_nonneg (hw x) (pow_nonneg (hf x) _))
  have hfirst:=weighted_lower_moment_absorption w f hw hf hmass n 1 (by omega) T B 8 hT
    (by simpa only [pow_one] using hB)
  have hsecond:=weighted_lower_moment_absorption w f hw hf hmass n 2 hn T C 8 hT hC
  have hscaled:=mul_le_mul_of_nonneg_left hrec (by norm_num:(0:ℝ)≤8)
  change 8*(B*(∑x,w x*f x^(n-1)))≤T^n+M at hfirst
  change 8*(C*(∑x,w x*f x^(n-2)))≤T^n+M at hsecond
  change M≤T^n
  change 0≤M at hM
  change 8*M≤8*(B*(∑x,w x*f x^(n-1))+C*(∑x,w x*f x^(n-2))+D+E) at hscaled
  linarith [pow_nonneg hT n]

end SpectralConsequences
