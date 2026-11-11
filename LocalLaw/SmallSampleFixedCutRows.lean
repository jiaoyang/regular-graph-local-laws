import LocalLaw.SmallSampleCutRows

/-! # A fixed core cap gives fixed cut mass for at most two selected vertices -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance smallSampleFixedCutDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace DeficientGraph
variable {V:Type} [Fintype V] {d:ℕ}

theorem small_sample_fixed_cut_rows (g:DeficientGraph V d)(hd:3≤d)(T:Set V)(q z:ℂ)(C:ℝ)(hC:0≤C)
    (hT:Nat.card T≤2)
    (hcore:letI:DecidableEq (Tᶜ:Set V):=fun a b=>Classical.propDecidable (a=b)
      ∀x y:(Tᶜ:Set V),‖(g.delete T).extensionGreen q z x y‖≤C) :
    letI:DecidableEq (Tᶜ:Set V):=fun a b=>Classical.propDecidable (a=b)
    ∀x:(Tᶜ:Set V),(∑b:T,‖((g.delete T).extensionGreen q z*g.H.submatrix
      (Subtype.val:(Tᶜ:Set V)→V) (Subtype.val:T→V)) x b‖)≤2*(d:ℝ)*C := by
  letI:DecidableEq (Tᶜ:Set V):=fun a b=>Classical.propDecidable (a=b)
  intro x
  have hdR:(3:ℝ)≤d:=Nat.cast_le.mpr hd
  have hsqrt:1≤Real.sqrt ((d:ℝ)-1):=by
    have hh:=Real.sq_sqrt (show 0≤(d:ℝ)-1 by linarith)
    nlinarith [Real.sqrt_nonneg ((d:ℝ)-1)]
  have hratio:(d:ℝ)/Real.sqrt ((d:ℝ)-1)≤d:=by
    apply (div_le_iff₀ (by linarith:0<Real.sqrt ((d:ℝ)-1))).mpr
    nlinarith [Nat.cast_nonneg (α:=ℝ) d]
  have hcol (b:T):‖((g.delete T).extensionGreen q z*g.H.submatrix
      (Subtype.val:(Tᶜ:Set V)→V) (Subtype.val:T→V)) x b‖≤C*(d:ℝ):=by
    exact (g.cut_coupling_far_column_bound T ((g.delete T).extensionGreen q z) x b
      C hC (fun v _=>hcore x v)).trans (mul_le_mul_of_nonneg_left hratio hC)
  have hn:(Fintype.card T:ℝ)≤2:=by exact_mod_cast (show Fintype.card T≤2 by simpa only[Nat.card_eq_fintype_card] using hT)
  calc
    _≤∑_b:T,C*(d:ℝ):=Finset.sum_le_sum (fun b _=>hcol b)
    _=(Fintype.card T:ℝ)*(C*(d:ℝ)):=by simp
    _≤2*(C*(d:ℝ)):=mul_le_mul_of_nonneg_right hn (by positivity)
    _=2*(d:ℝ)*C:=by ring

end DeficientGraph
end LocalLaw
