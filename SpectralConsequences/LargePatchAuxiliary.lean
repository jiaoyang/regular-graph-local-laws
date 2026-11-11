import SpectralConsequences.LargePatchParameters
import LocalLaw.UniversalBadCenterParameters
import LocalLaw.OffsetStructuralEvent

/-! The enlarged tree-count auxiliary event has every polynomial tail under
both the genuine uniform graph law and the original structural conditioning. -/
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance largePatchAuxiliaryDecidable (p:Prop):Decidable p:=Classical.propDecidable p

theorem logarithmicRadius_nat_mul_lower (t d N:ℕ)(β:ℝ)
    (hd:3≤d)(hN:1≤N)(hβ:0≤β):
    t*logarithmicRadius β d N≤logarithmicRadius ((t:ℝ)*β) d N:=by
  have hk:1<((d-1:ℕ):ℝ):=by exact_mod_cast (show 1<d-1 by omega)
  have hlog:0≤Real.log (N:ℝ):=Real.log_nonneg (by exact_mod_cast hN)
  have hcoord:0≤β*Real.log (N:ℝ)/Real.log ((d-1:ℕ):ℝ):=
    div_nonneg (mul_nonneg hβ hlog) (Real.log_pos hk).le
  unfold logarithmicRadius
  apply (Nat.le_floor_iff (by positivity:0≤(t:ℝ)*β*Real.log (N:ℝ)/Real.log ((d-1:ℕ):ℝ))).mpr
  have hh:=mul_le_mul_of_nonneg_left (Nat.floor_le hcoord) (Nat.cast_nonneg t)
  push_cast
  convert hh using 1
  ring

def LargeTreeCountAux {N d:ℕ}(c γ:ℝ)(g:LocalLaw.RegularGraph N d):Prop:=
  (nonTreeCenters g.graph (2*logarithmicRadius (c/4) d N+1)).card≤⌊(N:ℝ)^γ⌋₊

/-- The count at 2 floor(R)+1 is dominated by the unconditional fixed-offset
count at the genuinely larger logarithmic radius. -/
theorem eventually_largeTreeCountAux_failure (d p:ℕ)(c γ:ℝ)
    (hd:3≤d)(hc:0≤c)(hγ:3*c/2<γ):
    ∀ᶠ N:ℕ in Filter.atTop,
      eventMass (LocalLaw.RegularGraph.weight (N:=N) (d:=d))
        (fun g=>¬LargeTreeCountAux c γ g)≤1/(N:ℝ)^p:=by
  filter_upwards [eventually_universal_badCenter_probability d 1 p (2*c) γ hd (by linarith) (by linarith),
    Filter.eventually_ge_atTop 1] with N hprob hN
  have hrad:2*logarithmicRadius (c/4) d N+1≤logarithmicRadius ((2*c)/4) d N+1:=by
    have hh:=logarithmicRadius_nat_mul_lower 2 d N (c/4) hd hN (by linarith)
    rw [show ((2:ℕ):ℝ)*(c/4)=(2*c)/4 by norm_num;ring] at hh
    exact Nat.add_le_add_right hh 1
  have hsub:∀g:LocalLaw.RegularGraph N d,¬LargeTreeCountAux c γ g→
      (N:ℝ)^γ<((nonTreeCenters g.graph (logarithmicRadius ((2*c)/4) d N+1)).card:ℝ):=by
    intro g hg
    apply lt_of_not_ge
    intro hle
    have hcard:((nonTreeCenters g.graph (2*logarithmicRadius (c/4) d N+1)).card:ℝ)≤(N:ℝ)^γ:=by
      have hh:((nonTreeCenters g.graph (2*logarithmicRadius (c/4) d N+1)).card:ℝ)≤
          ((nonTreeCenters g.graph (logarithmicRadius ((2*c)/4) d N+1)).card:ℝ):=by
        exact_mod_cast Finset.card_le_card (nonTreeCenters_mono g.graph hrad)
      exact hh.trans hle
    exact hg ((Nat.le_floor_iff (Real.rpow_nonneg (Nat.cast_nonneg N) γ)).mpr hcard)
  exact (eventMass_mono LocalLaw.RegularGraph.weight LocalLaw.RegularGraph.weight_nonnegative hsub).trans hprob

/-- The original source event is retained in the denominator. Its already
proved positive mass turns the unconditional auxiliary tail into this bound. -/
theorem eventually_largeTreeCountAux_original_conditional_failure (d ω p:ℕ)(cOriginal c γ:ℝ)
    (hd:3≤d)(hω:1≤ω)(hcOriginal:0<cOriginal)(hcOriginal1:cOriginal<1)
    (hc:0≤c)(hγ:3*c/2<γ):
    ∀ᶠ N:ℕ in Filter.atTop,Nonempty (LocalLaw.RegularGraph N d)→
      eventMass (LocalLaw.RegularGraph.weight (N:=N) (d:=d)) (fun g=>
        LocalLaw.RegularGraph.structural (logarithmicRadius (cOriginal/4) d N) ω ⌊(N:ℝ)^cOriginal⌋₊ g ∧
          ¬LargeTreeCountAux c γ g)/
      eventMass (LocalLaw.RegularGraph.weight (N:=N) (d:=d))
        (LocalLaw.RegularGraph.structural (logarithmicRadius (cOriginal/4) d N) ω ⌊(N:ℝ)^cOriginal⌋₊)≤
        2/(N:ℝ)^p:=by
  filter_upwards [eventually_largeTreeCountAux_failure d p c γ hd hc hγ,
    eventually_original_structural_mass_half d ω cOriginal hd hω hcOriginal hcOriginal1,
    Filter.eventually_ge_atTop 1] with N htail hmass hN
  intro hnonempty
  have hnum:=eventMass_mono LocalLaw.RegularGraph.weight LocalLaw.RegularGraph.weight_nonnegative
    (fun (g:LocalLaw.RegularGraph N d) (hg:LocalLaw.RegularGraph.structural (logarithmicRadius (cOriginal/4) d N) ω ⌊(N:ℝ)^cOriginal⌋₊ g ∧
      ¬LargeTreeCountAux c γ g)=>hg.2)
  have hden:=hmass hnonempty
  have hn:0<(N:ℝ):=Nat.cast_pos.mpr (by omega)
  exact (div_le_div₀ (by positivity) (hnum.trans htail) (by norm_num:0<(1/2:ℝ)) hden).trans_eq (by ring)

end SpectralConsequences
#print axioms SpectralConsequences.eventually_largeTreeCountAux_original_conditional_failure
