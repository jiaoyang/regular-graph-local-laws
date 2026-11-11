import LocalLaw.BoundaryMaxProfile

/-! # Higher-power nonlinear remainder budgets with the same source parameters -/

namespace LocalLaw

private theorem source_square_error_power (a r p : ℕ) (L ε H : ℝ)
    (hL : 1≤L) (hε : 0≤ε) (hH : 0≤H) (hcap : ε*L^(4*a)≤1)
    (hp : r+p+1≤4*a) (hlarge : 2*H≤L) : H*ε^2*L^r≤ε/(2*L^p) := by
  have hLp : 0<L := by linarith
  have hscale := (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL hp) hε).trans hcap
  have hfirst := mul_le_mul_of_nonneg_left hscale (mul_nonneg hH hε)
  have hsecond := mul_le_mul_of_nonneg_right hlarge hε
  apply (le_div_iff₀ (show 0<2*L^p by positivity)).mpr
  apply (mul_le_mul_right hLp).mp
  have hid : (H*ε^2*L^r*(2*L^p))*L=2*H*ε^2*L^(r+p+1) := by
    rw [pow_add,pow_add,pow_one]; ring
  rw [hid]
  nlinarith only [hfirst,hsecond]

theorem boundary_max_parameter_budgets_power (a p : ℕ) (L ε n M e S W U M0 E W0 : ℝ)
    (ha : 12≤a) (hp : a+p+12≤4*a) (hL : 1≤L) (hε : 0≤ε)
    (hn : 0≤n) (hM : 0≤M) (he : 0≤e) (hS : 0≤S) (hW : 0≤W)
    (hU : 0≤U) (hM0 : 0≤M0) (hE : 0≤E) (hW0 : 0≤W0)
    (hcap : ε*L^(4*a)≤1) (hcount : n≤U*L^(2*a)) (hroot : M*Real.sqrt n≤M0)
    (herror : e≤E*L^5*ε) (hsquare : S^2≤n*W) (hrow : W≤W0*L)
    (hlargeFeedback : 2*(E*(U+W0+1))≤L)
    (hlargeRemainder : 2*(2*M0*(U+1)*E^2*W0)≤L) :
    e*S≤1/2 ∧ 2*M*e^2*S^2≤ε/(2*L^p) := by
  have hsmall := (boundary_max_parameter_budgets a L ε n M e S W U M0 E W0 ha hL hε hn hM he hS hW
    hU hM0 hE hW0 hcap hcount hroot herror hsquare hrow hlargeFeedback hlargeRemainder).1
  have hL0 : 0≤L := by linarith
  let H := 2*M0*(U+1)*E^2*W0
  have hH : 0≤H := by dsimp only [H]; positivity
  have hsqrtn : Real.sqrt n≤(U+1)*L^a := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    have hh := mul_le_mul_of_nonneg_right (show U≤(U+1)^2 by nlinarith only [hU]) (pow_nonneg hL0 (2*a))
    have hid : 2*a=a*2 := by omega
    rw [hid,pow_mul] at hcount hh
    exact hcount.trans (hh.trans_eq (by ring))
  have hMn : M*n≤M0*((U+1)*L^a) := by
    calc
      _ = (M*Real.sqrt n)*Real.sqrt n := by rw [mul_assoc,Real.mul_self_sqrt hn]
      _ ≤ _ := mul_le_mul hroot hsqrtn (Real.sqrt_nonneg n) hM0
  have hrem : 2*M*e^2*S^2≤H*ε^2*L^(a+11) := by
    calc
      _ ≤ 2*M*e^2*(n*W) := mul_le_mul_of_nonneg_left hsquare (by positivity)
      _ = 2*(M*n)*e^2*W := by ring
      _ ≤ 2*(M0*((U+1)*L^a))*(E*L^5*ε)^2*(W0*L) :=
        mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hMn (by norm_num))
          (pow_le_pow_left₀ he herror 2) (sq_nonneg e) (by positivity)) hrow hW (by positivity)
      _ = _ := by
        rw [show a+11=a+10+1 by omega,pow_add,pow_add,pow_one]
        dsimp only [H]; ring
  exact ⟨hsmall,hrem.trans (source_square_error_power a (a+11) p L ε H hL hε hH hcap (by omega) hlargeRemainder)⟩

open scoped BigOperators

theorem BoundaryMaxProfile.bootstrap_power {I F : Type*} [Fintype F]
    (P R : Matrix I I ℂ) (l : F → I) (root : I) (a p : ℕ) (L U M0 W0 ε E e : ℝ)
    (profile : BoundaryMaxProfile P l root a L U M0 W0) (D : Matrix F F ℂ) (c : ℂ)
    (ha : 12≤a) (hp : a+p+12≤4*a) (hL : 1≤L) (hε : 0≤ε)
    (hU : 0≤U) (hM0 : 0≤M0) (hW0 : 0≤W0) (hE : 0≤E) (he : 0≤e) (hc : ‖c‖≤1)
    (hcap : ε*L^(4*a)≤1) (herror : e≤E*L^5*ε) (hD : ∀ β,∑ α,‖D α β‖≤e)
    (hidentity : ∀ j,R root j-P root j=c*(∑ α,∑ β,P root (l α)*D α β*P (l β) j)+
      c*(∑ α,∑ β,(R root (l α)-P root (l α))*D α β*P (l β) j))
    (hlargeFeedback : 2*(E*(U+W0+1))≤L)
    (hlargeRemainder : 2*(2*M0*(U+1)*E^2*W0)≤L) :
    (∀ α,‖R root (l α)-P root (l α)‖≤2*profile.M*e*profile.S) ∧
      ∀ j,‖c*(∑ α,∑ β,(R root (l α)-P root (l α))*D α β*P (l β) j)‖≤ε/(2*L^p) := by
  have hnum := boundary_max_parameter_budgets_power a p L ε (Fintype.card F) profile.M e profile.S profile.W
    U M0 E W0 ha hp hL hε (Nat.cast_nonneg _) profile.root_nonnegative he profile.column_nonnegative
    profile.square_nonnegative hU hM0 hE hW0 hcap profile.count profile.root_count herror
    profile.column_square profile.row_log hlargeFeedback hlargeRemainder
  have hboot := boundary_row_max_and_remainder R P l D c root profile.M e profile.S profile.root_nonnegative
    he profile.column_nonnegative hc profile.root_bound hD profile.column_bound hidentity hnum.1
  exact ⟨hboot.1,fun j => (hboot.2 j).trans hnum.2⟩

end LocalLaw
