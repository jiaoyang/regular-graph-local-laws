import SpectralConsequences.ThreeTermMomentBootstrap
import SpectralConsequences.FluctuationMomentBootstrap

/-! The drift plus square-root-variance fluctuation scale follows from the
three actual lower-moment terms, including a small additive exception. -/
open scoped BigOperators
noncomputable section
namespace SpectralConsequences

theorem three_term_fluctuation_bound {X:Type*}[Fintype X]
    (w f:X→ℝ) (hw:∀x,0≤w x) (hf:∀x,0≤f x) (hmass:∑x,w x≤1)
    (n:ℕ) (hn:2≤n) (B C ε V E K:ℝ)
    (hB:0≤B) (hC:0≤C) (hε:0≤ε) (hV:0≤V) (hVε:V≤ε)
    (hE:E≤B^n) (hK:8≤K) (hKC:8*C≤K)
    (hrec:(∑x,w x*f x^n)≤B*(∑x,w x*f x^(n-1))+
      (C*ε*V)*(∑x,w x*f x^(n-2))+C*ε*V^(n-1)+E):
    (∑x,w x*f x^n)≤(K*(B+Real.sqrt (ε*V)))^n:=by
  let S:=Real.sqrt (ε*V)
  let T:=K*(B+S)
  have hS:0≤S:=Real.sqrt_nonneg _
  have hSsq:S^2=ε*V:=Real.sq_sqrt (mul_nonneg hε hV)
  have hK1:1≤K:=by linarith
  have hK0:0≤K:=by linarith
  have hT:0≤T:=by dsimp only [T];positivity
  have hsum:0≤B+S:=add_nonneg hB hS
  have hpowK:K≤K^n:=by
    calc
      _=K^1:=by rw [pow_one]
      _≤K^n:=pow_le_pow_right₀ hK1 (by omega)
  have hKB:8*B≤T:=by dsimp only [T];nlinarith [mul_nonneg hK0 hS]
  have hKV:8*(C*ε*V)≤T^2:=by
    have hscale:8*C≤K^2:=(hKC.trans (by nlinarith))
    have hh:=mul_le_mul hscale (pow_le_pow_left₀ hS (le_add_of_nonneg_left hB) 2)
      (sq_nonneg S) (sq_nonneg K)
    dsimp only [T]
    rw [mul_pow]
    apply le_trans _ hh
    rw [hSsq]
    ring_nf
    exact le_rfl
  have hKD:8*(C*ε*V^(n-1))≤T^n:=by
    have hincr:=fluctuation_increment_power_bound ε V hε hV hVε (n-1) (by omega)
    have hincr':ε*V^(n-1)≤S^n:=by simpa only [Nat.sub_add_cancel (show 1≤n by omega)] using hincr
    have hco:8*C≤K^n:=hKC.trans hpowK
    calc
      _=(8*C)*(ε*V^(n-1)):=by ring
      _≤(8*C)*S^n:=mul_le_mul_of_nonneg_left hincr' (by positivity)
      _≤K^n*(B+S)^n:=mul_le_mul hco (pow_le_pow_left₀ hS (le_add_of_nonneg_left hB) n)
        (pow_nonneg hS n) (pow_nonneg hK0 n)
      _=T^n:=(mul_pow K (B+S) n).symm
  have hKE:8*E≤T^n:=by
    have hco:8≤K^n:=hK.trans hpowK
    calc
      _≤8*B^n:=mul_le_mul_of_nonneg_left hE (by norm_num)
      _≤K^n*(B+S)^n:=mul_le_mul hco (pow_le_pow_left₀ hB (le_add_of_nonneg_right hS) n)
        (pow_nonneg hB n) (pow_nonneg hK0 n)
      _=T^n:=(mul_pow K (B+S) n).symm
  exact finite_three_term_moment_bound w f hw hf hmass n hn B (C*ε*V) (C*ε*V^(n-1)) E T
    hT hKB hKV hKD hKE hrec

end SpectralConsequences
