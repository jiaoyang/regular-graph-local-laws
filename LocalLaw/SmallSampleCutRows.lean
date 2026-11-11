import LocalLaw.LeafCoreFarAdapter

/-! # At most two sampled vertices give logarithmic true coupling rows -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance smallSampleCutRowsDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace DeficientGraph
variable {V:Type} [Fintype V] [DecidableEq V] {d:ℕ}

omit [DecidableEq V] in
theorem small_sample_cut_rows (g:DeficientGraph V d)(hd:3≤d)(T:Set V)
    (q z:ℂ)(K L ε:ℝ)(hK:0≤K)(hL:0≤L)(_hε:0≤ε)(hεone:ε≤1)
    (hT:Nat.card T≤2)(hcore:g.LeafCoreDecayBound T q z K L ε) :
    letI:DecidableEq (Tᶜ:Set V):=fun a b=>Classical.propDecidable (a=b)
    ∀x:(Tᶜ:Set V),(∑b:T,‖((g.delete T).extensionGreen q z*g.H.submatrix
      (Subtype.val:(Tᶜ:Set V)→V) (Subtype.val:T→V)) x b‖)≤4*(d:ℝ)*K*L := by
  letI:DecidableEq (Tᶜ:Set V):=fun a b=>Classical.propDecidable (a=b)
  intro x
  have hF:0≤2*K*L:=by positivity
  have hpoint (v:(Tᶜ:Set V)):‖(g.delete T).extensionGreen q z x v‖≤2*K*L:=by
    have hh:=hcore x v 0 (by simp)
    simp only[pow_zero,mul_one] at hh
    have hs:K*L*ε≤K*L:=mul_le_of_le_one_right (mul_nonneg hK hL) hεone
    exact hh.trans (by linarith)
  have hdR:(3:ℝ)≤d:=Nat.cast_le.mpr hd
  have hsqrt:1≤Real.sqrt ((d:ℝ)-1):=by
    have hh:=Real.sq_sqrt (show 0≤(d:ℝ)-1 by linarith)
    nlinarith [Real.sqrt_nonneg ((d:ℝ)-1)]
  have hratio:(d:ℝ)/Real.sqrt ((d:ℝ)-1)≤d:=by
    apply (div_le_iff₀ (by linarith:0<Real.sqrt ((d:ℝ)-1))).mpr
    nlinarith [Nat.cast_nonneg (α:=ℝ) d]
  have hcol (b:T):‖((g.delete T).extensionGreen q z*g.H.submatrix
      (Subtype.val:(Tᶜ:Set V)→V) (Subtype.val:T→V)) x b‖≤(2*K*L)*(d:ℝ):=by
    exact (g.cut_coupling_far_column_bound T ((g.delete T).extensionGreen q z) x b
      (2*K*L) hF (fun v _=>hpoint v)).trans (mul_le_mul_of_nonneg_left hratio hF)
  have hn:(Fintype.card T:ℝ)≤2:=by exact_mod_cast (show Fintype.card T≤2 by simpa only[Nat.card_eq_fintype_card] using hT)
  calc
    _≤∑_b:T,(2*K*L)*(d:ℝ):=Finset.sum_le_sum (fun b _=>hcol b)
    _=(Fintype.card T:ℝ)*((2*K*L)*(d:ℝ)):=by simp
    _≤2*((2*K*L)*(d:ℝ)):=mul_le_mul_of_nonneg_right hn (by positivity)
    _=4*(d:ℝ)*K*L:=by ring

end DeficientGraph
end LocalLaw
