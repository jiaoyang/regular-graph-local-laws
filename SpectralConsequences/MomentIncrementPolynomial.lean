import SpectralConsequences.ComplexMomentAlgebra
import SpectralConsequences.ExchangeableSiteIdentity
import SpectralConsequences.FiniteMeanAlgebra

/-! # The genuine symmetric-increment contribution to high moments

Only local observable increments and global residual increments enter the
estimate. The moment itself is not a hypothesis.
-/
open scoped BigOperators
noncomputable section
namespace SpectralConsequences
open LocalLaw

theorem nonnegative_add_power_endpoint (x y:ℝ) (hx:0≤x) (hy:0≤y) (n:ℕ):
    (x+y)^n≤2^n*(x^n+y^n):=by
  by_cases hxy:x≤y
  · calc
      _≤(2*y)^n:=pow_le_pow_left₀ (by positivity) (by linarith) _
      _=2^n*y^n:=mul_pow _ _ _
      _≤_:=mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (pow_nonneg hx _)) (by positivity)
  · have hyx:y≤x:=(lt_of_not_ge hxy).le
    calc
      _≤(2*x)^n:=pow_le_pow_left₀ (by positivity) (by linarith) _
      _=2^n*x^n:=mul_pow _ _ _
      _≤_:=mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (pow_nonneg hy _)) (by positivity)

def momentIncrementCoefficient (p:ℕ):ℝ:=((2*p-1:ℕ):ℝ)*2^(2*p-2)

theorem complex_moment_increment_polynomial (p:ℕ) (hp:1≤p)
    (h k x y:ℂ) (ε A:ℝ) (hε:0≤ε) (hA:0≤A)
    (hlocal:‖h-k‖≤ε) (hglobal:‖x-y‖≤A):
    ‖(h-k)*(complexMomentTest p x-complexMomentTest p y)‖≤
      momentIncrementCoefficient p*ε*A*(‖x‖^(2*p-2)+A^(2*p-2)):=by
  rw [norm_mul]
  have ht:=complexMomentTest_difference_bound p hp x y
  have hpw:(‖x‖+‖x-y‖)^(2*p-2)≤2^(2*p-2)*(‖x‖^(2*p-2)+A^(2*p-2)):=
    (pow_le_pow_left₀ (by positivity) (add_le_add_left hglobal _) _).trans
      (nonnegative_add_power_endpoint ‖x‖ A (norm_nonneg _) hA _)
  calc
    _≤ε*(((2*p-1:ℕ):ℝ)*‖x-y‖*(‖x‖+‖x-y‖)^(2*p-2)):=
      mul_le_mul hlocal ht (norm_nonneg _) hε
    _≤ε*(((2*p-1:ℕ):ℝ)*A*(2^(2*p-2)*(‖x‖^(2*p-2)+A^(2*p-2)))):=by
      apply mul_le_mul_of_nonneg_left _ hε
      exact mul_le_mul (mul_le_mul_of_nonneg_left hglobal (Nat.cast_nonneg _)) hpw
        (by positivity) (by positivity)
    _=_:=by dsimp only [momentIncrementCoefficient];ring

theorem reversibleExtension_real_expectation {X:Type*} [Fintype X] (w:X→ℝ)
    (E:ReversibleExtension X w) (f:X→ℝ):
    (∑ω,E.weight ω*f (E.project ω))=∑x,w x*f x:=by
  have hh:=reversibleExtension_expectation w E (fun x=>(f x:ℂ))
  have hc:=congrArg Complex.re hh
  simpa only [finiteExpectation,Complex.re_sum,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,sub_zero] using hc

theorem reversible_symmetric_moment_increment {X:Type*} [Fintype X]
    (w:X→ℝ) (E:ReversibleExtension X w) (Ω A:X→Prop)
    [DecidablePred Ω] [DecidablePred A] (hAΩ:∀x,A x→Ω x)
    (h F:X→ℂ) (p:ℕ) (hp:1≤p) (ε V:ℝ) (hε:0≤ε) (hV:0≤V)
    (hlocal:∀ω,A (E.project ω)→A (E.project (E.switching ω))→
      ‖h (E.project ω)-h (E.project (E.switching ω))‖≤ε)
    (hglobal:∀ω,A (E.project ω)→A (E.project (E.switching ω))→
      ‖F (E.project ω)-F (E.project (E.switching ω))‖≤V):
    ‖finiteExpectation E.weight (fun ω=>
      if A (E.project ω) ∧ A (E.project (E.switching ω)) then
        (h (E.project ω)-h (E.project (E.switching ω)))*
          (complexMomentTest p (F (E.project ω))-complexMomentTest p (F (E.project (E.switching ω))))
      else 0)‖≤
      momentIncrementCoefficient p*ε*V*
        ((∑x,if Ω x then w x*‖F x‖^(2*p-2) else 0)+V^(2*p-2)*eventMass w Ω):=by
  classical
  let K:=momentIncrementCoefficient p*ε*V
  have hK:0≤K:=by dsimp only [K,momentIncrementCoefficient];positivity
  apply (finiteExpectation_norm_le E.weight E.nonnegative _).trans
  calc
    _≤∑ω,E.weight ω*(if Ω (E.project ω) then
        K*(‖F (E.project ω)‖^(2*p-2)+V^(2*p-2)) else 0):=by
      apply Finset.sum_le_sum
      intro ω _
      apply mul_le_mul_of_nonneg_left _ (E.nonnegative ω)
      by_cases ha:A (E.project ω) ∧ A (E.project (E.switching ω))
      · rw [if_pos ha,if_pos (hAΩ _ ha.1)]
        exact complex_moment_increment_polynomial p hp _ _ _ _ ε V hε hV
          (hlocal ω ha.1 ha.2) (hglobal ω ha.1 ha.2)
      · rw [if_neg ha,norm_zero]
        split_ifs <;>positivity
    _=∑x,w x*(if Ω x then K*(‖F x‖^(2*p-2)+V^(2*p-2)) else 0):=
      reversibleExtension_real_expectation w E
        (fun x=>if Ω x then K*(‖F x‖^(2*p-2)+V^(2*p-2)) else 0)
    _=_:=by
      change (∑x,w x*(if Ω x then K*(‖F x‖^(2*p-2)+V^(2*p-2)) else 0))=
        K*((∑x,if Ω x then w x*‖F x‖^(2*p-2) else 0)+V^(2*p-2)*eventMass w Ω)
      rw [mul_add]
      simp only [eventMass,Finset.mul_sum]
      rw [←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx:Ω x <;>simp only [hx,if_true,if_false,mul_zero,zero_add,add_zero]
      ring

end SpectralConsequences
