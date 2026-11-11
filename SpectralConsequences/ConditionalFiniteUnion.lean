import LocalLaw.Abstract
import SpectralConsequences.ExteriorMesh

/-! Conditional union bounds retain the original event denominator exactly. -/
open scoped BigOperators
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance conditionalFiniteUnionDecidable (p:Prop):Decidable p:=Classical.propDecidable p
variable {Ω I:Type*}[Fintype Ω]

theorem conditional_finite_union (w:Ω→ℝ)(hw:∀x,0≤w x)(original:Ω→Prop)
    (grid:Finset I)(good:I→Ω→Prop)(δ:ℝ)
    (hpoint:∀i∈grid,eventMass w (fun x=>original x ∧¬good i x)/eventMass w original≤δ):
    eventMass w (fun x=>original x ∧¬∀i∈grid,good i x)/eventMass w original≤
      (grid.card:ℝ)*δ:=by
  have hden:0≤eventMass w original:=by
    unfold eventMass
    apply Finset.sum_nonneg
    intro x _
    split_ifs
    · exact hw x
    · exact le_rfl
  have hcover:∀x:Ω,(original x ∧¬∀i∈grid,good i x)→
      ∃i∈grid,original x ∧¬good i x:=by
    intro x hx
    have hex:∃i∈grid,¬good i x:=by
      by_contra hnone
      apply hx.2
      intro i hi
      by_contra hbad
      exact hnone ⟨i,hi,hbad⟩
    obtain ⟨i,hi,hbad⟩:=hex
    exact ⟨i,hi,hx.1,hbad⟩
  have hm: eventMass w (fun x=>original x ∧¬∀i∈grid,good i x)≤
      ∑i∈grid,eventMass w (fun x=>original x ∧¬good i x):=
    (eventMass_mono w hw hcover).trans (eventMass_exists_finset_le grid w hw _)
  calc
    _≤(∑i∈grid,eventMass w (fun x=>original x ∧¬good i x))/eventMass w original:=
      div_le_div_of_nonneg_right hm hden
    _=∑i∈grid,eventMass w (fun x=>original x ∧¬good i x)/eventMass w original:=by
      rw [Finset.sum_div]
    _≤∑i∈grid,δ:=Finset.sum_le_sum hpoint
    _=(grid.card:ℝ)*δ:=by simp

theorem conditional_polynomial_mesh (w:Ω→ℝ)(hw:∀x,0≤w x)(original:Ω→Prop)
    (N D:ℕ)(hN:1≤N)(grid:Finset I)(hcard:grid.card≤N^3)(good:I→Ω→Prop)
    (hpoint:∀i∈grid,eventMass w (fun x=>original x ∧¬good i x)/eventMass w original≤
      1/(N:ℝ)^(D+3)):
    eventMass w (fun x=>original x ∧¬∀i∈grid,good i x)/eventMass w original≤1/(N:ℝ)^D:=by
  have hNp:0<(N:ℝ):=Nat.cast_pos.mpr (by omega)
  apply (conditional_finite_union w hw original grid good _ hpoint).trans
  have hc:(grid.card:ℝ)≤(N:ℝ)^3:=by exact_mod_cast hcard
  calc
    _≤(N:ℝ)^3*(1/(N:ℝ)^(D+3)):=mul_le_mul_of_nonneg_right hc (by positivity)
    _=1/(N:ℝ)^D:=by rw [pow_add];field_simp;ring

end SpectralConsequences
