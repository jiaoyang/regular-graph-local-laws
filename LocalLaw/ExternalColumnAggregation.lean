import LocalLaw.SampledErrorColumns

/-! Fixed-target and global-good exceptions in an actual boundary column. -/
open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance externalColumnAggregationDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {I : Type} [Fintype I]

theorem external_column_two_exception_sum (f : I→ℂ) (good exceptions : Finset I)
    (δ Bfar : ℝ) (hδ : 0≤δ) (hBfar : 0≤Bfar)
    (hcap : ∀ i, ‖f i‖≤δ) (hfar : ∀ i, i∈good→i∉exceptions→‖f i‖≤Bfar) :
    (∑ i, ‖f i‖)≤(((Finset.univ\good).card+exceptions.card:ℕ):ℝ)*δ+(Fintype.card I:ℝ)*Bfar := by
  let bad:=(Finset.univ\good)∪exceptions
  have hh:=finite_exceptional_entry_sum f bad δ Bfar hBfar hcap (by
    intro i hi
    have hg : i∈good := by
      by_contra hn
      exact hi (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hn⟩))
    exact hfar i hg (fun he => hi (Finset.mem_union_right _ he)))
  have hcard : (bad.card:ℝ)≤(((Finset.univ\good).card+exceptions.card:ℕ):ℝ) := by
    exact_mod_cast (Finset.card_union_le (Finset.univ\good) exceptions)
  exact hh.trans (add_le_add_right (mul_le_mul_of_nonneg_right hcard hδ) _)

theorem external_column_log_budget (f : I→ℂ) (good exceptions : Finset I)
    (L εprime δ Bfar D Kbad Kexc Kfar : ℝ)
    (hL : 1≤L) (hε : 0≤εprime) (hδ : 0≤δ) (hBfar : 0≤Bfar)
    (_hD : 0≤D) (hKbad : 0≤Kbad) (hKexc : 0≤Kexc) (hKfar : 0≤Kfar)
    (hcap : ∀ i, ‖f i‖≤δ) (hfar : ∀ i, i∈good→i∉exceptions→‖f i‖≤Bfar)
    (hbad : ((Finset.univ\good).card:ℝ)≤Kbad*L^2)
    (hexc : (exceptions.card:ℝ)≤Kexc*L)
    (hdelta : δ≤D*εprime) (hfarSum : (Fintype.card I:ℝ)*Bfar≤Kfar*εprime) :
    (∑ i, ‖f i‖)≤(Kbad*D+Kexc*D+Kfar)*L^2*εprime := by
  have hL2 : L≤L^2 := by nlinarith
  have hone : 1≤L^2 := one_le_pow₀ hL
  have hcount : (((Finset.univ\good).card+exceptions.card:ℕ):ℝ)≤(Kbad+Kexc)*L^2 := by
    push_cast
    nlinarith only [hbad,hexc,mul_le_mul_of_nonneg_left hL2 hKexc]
  have hh:=external_column_two_exception_sum f good exceptions δ Bfar hδ hBfar hcap hfar
  calc
    _ ≤ (((Finset.univ\good).card+exceptions.card:ℕ):ℝ)*δ+(Fintype.card I:ℝ)*Bfar := hh
    _ ≤ ((Kbad+Kexc)*L^2)*(D*εprime)+Kfar*εprime :=
      add_le_add (mul_le_mul hcount hdelta hδ (by positivity)) hfarSum
    _ ≤ ((Kbad+Kexc)*L^2)*(D*εprime)+Kfar*(L^2*εprime) :=
      add_le_add_left (mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hε hone) hKfar) _
    _ = _ := by ring

end LocalLaw
