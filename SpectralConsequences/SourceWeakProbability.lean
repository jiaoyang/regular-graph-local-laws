import LocalLaw.SourceFirstStageProof
import LocalLaw.SourceBoundedBootstrapReduction
import LocalLaw.StructuralEventTransfer
import LocalLaw.PolynomialFailureAbsorption

/-! The internal coefficient-one weak event has every polynomial failure
bound. This retains the actual Q prior and shortened finite model radius,
rather than inferring a Q field from the final entry/trace theorem. -/
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance sourceWeakProbabilityDecidable (p:Prop):Decidable p:=Classical.propDecidable p

theorem source_uniform_weak_failure (a b d:ℕ)(c β B:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hc:0<c)(hc1:c<1)(hβ:0<β)
    (hβc:β≤c/32)(hB:2*(d:ℝ)≤B):
    ∀D:ℕ,∀ᶠ N:ℕ in Filter.atTop,∀badCount:ℕ,
      eventMass (RegularGraph.weight (N:=N) (d:=d)) (fun g=>
        RegularGraph.structural (logarithmicRadius (c/4) d N) (finiteOmega d) badCount g ∧
          ¬∀z∈boundedLocalLawDomain N b B,
            (graphLocalLawFamilyWithRadii N d a (effectiveModelRadius a d N β)
              (logarithmicRadius β d N)).weak z g)≤1/(N:ℝ)^D:=by
  intro D
  let γ:=7*c/8
  have hγ:3*c/4<γ:=by dsimp only [γ];linarith
  have hγ1:γ<1:=by dsimp only [γ];linarith
  have hgap:γ+β<1:=by dsimp only [γ];linarith
  have hB0:0≤B:=by have hh:=(Nat.cast_le (α:=ℝ)).mpr hd;linarith
  obtain ⟨Cq,C1,hCq,hC1,hCdel,hfirst⟩:=
    source_first_stage_all_powers a b d c β γ (2*B) ha hb hd hc hc1 hβ hβc
      (by linarith) hγ1 (by positivity) (D+39)
  have hgrid:0≤bootstrapGridConstant B:=by unfold bootstrapGridConstant;positivity
  filter_upwards [eventually_source_bounded_weak_of_first_stage a b d (D+39) Cq c β γ B C1
      ha hb hd (by omega) hc hc1 hβ hβc (by linarith) hgap hB hC1 hCdel hCq hfirst,
    eventually_offset_structural_difference d (finiteOmega d) 1 (D+1) c γ hd hc.le hγ,
    eventually_const_div_pow_succ_le (1+9*bootstrapGridConstant B) D,
    Filter.eventually_ge_atTop 1] with N huniform hoff habsorb hN
  intro badCount
  let failure:RegularGraph N d→Prop:=fun g=>¬∀z∈boundedLocalLawDomain N b B,
    (graphLocalLawFamilyWithRadii N d a (effectiveModelRadius a d N β)
      (logarithmicRadius β d N)).weak z g
  have hi:eventMass (RegularGraph.weight (N:=N) (d:=d)) (fun g=>
      RegularGraph.offsetStructural (logarithmicRadius (c/4) d N) (finiteOmega d) 1 ⌊(N:ℝ)^γ⌋₊ g ∧
      failure g)≤9*bootstrapGridConstant B/(N:ℝ)^(D+2):=by
    simpa only [show D+39-37=D+2 by omega] using huniform
  have hraw:=strengthened_event_failure_mass RegularGraph.weight RegularGraph.weight_nonnegative
    (RegularGraph.structural (logarithmicRadius (c/4) d N) (finiteOmega d) badCount)
    (RegularGraph.offsetStructural (logarithmicRadius (c/4) d N) (finiteOmega d) 1 ⌊(N:ℝ)^γ⌋₊)
    failure (1/(N:ℝ)^(D+1)) (9*bootstrapGridConstant B/(N:ℝ)^(D+2)) (hoff badCount) hi
  apply hraw.trans
  have hNp:0<(N:ℝ):=Nat.cast_pos.mpr (by omega)
  have hN1:1≤(N:ℝ):=Nat.one_le_cast.mpr hN
  have hstep:9*bootstrapGridConstant B/(N:ℝ)^(D+2)≤
      9*bootstrapGridConstant B/(N:ℝ)^(D+1):=
    div_le_div_of_nonneg_left (by positivity) (pow_pos hNp _)
      (pow_le_pow_right₀ hN1 (by omega))
  calc
    _≤1/(N:ℝ)^(D+1)+9*bootstrapGridConstant B/(N:ℝ)^(D+1):=add_le_add_left hstep _
    _=(1+9*bootstrapGridConstant B)/(N:ℝ)^(D+1):=by ring
    _≤_:=habsorb

theorem source_point_weak_failure (a b d:ℕ)(c β B:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hc:0<c)(hc1:c<1)(hβ:0<β)
    (hβc:β≤c/32)(hB:2*(d:ℝ)≤B):
    ∀D:ℕ,∀ᶠ N:ℕ in Filter.atTop,∀(z:ℂ),0<z.im→‖z‖≤B→
      Real.log (N:ℝ)^b/(N:ℝ)≤z.im→∀badCount:ℕ,
      eventMass (RegularGraph.weight (N:=N) (d:=d)) (fun g=>
        RegularGraph.structural (logarithmicRadius (c/4) d N) (finiteOmega d) badCount g ∧
          ¬g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
            (logarithmicRadius (c/4) d N) (finiteOmega d) badCount z)≤1/(N:ℝ)^D:=by
  intro D
  filter_upwards [source_uniform_weak_failure a b d c β B ha hb hd hc hc1 hβ hβc hB D]
    with N hprob
  intro z _ hzB hfloor badCount
  apply (eventMass_mono RegularGraph.weight RegularGraph.weight_nonnegative ?_).trans (hprob badCount)
  intro g hg
  exact ⟨hg.1,fun hall=>hg.2 ⟨hg.1,hall z ⟨hzB,hfloor⟩⟩⟩

end SpectralConsequences
#print axioms SpectralConsequences.source_point_weak_failure
