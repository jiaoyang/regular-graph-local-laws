import SpectralConsequences.SourceTheorem14

/-! The normalized sup-norm form of the actual graph delocalization theorem. -/
open scoped BigOperators
open Matrix
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance sourceDelocalizationSupnormDecidable (p:Prop):Decidable p:=Classical.propDecidable p

def SourceNormalizedDelocalized {N d:ℕ}(g:LocalLaw.RegularGraph N d):Prop:=
  ∀eig:ℝ,∀v:Fin N→ℂ,g.H *ᵥ v=(eig:ℂ) • v→(∑j,‖v j‖^2)=1→∀i:Fin N,
    ‖v i‖≤Real.sqrt (sourceEigenvectorConstant d)*Real.log (N:ℝ)^150/Real.sqrt (N:ℝ)

theorem sourceDelocalized_normalized {N d:ℕ}(g:LocalLaw.RegularGraph N d)
    (hd:3≤d)(hN:1≤N)(hg:SourceDelocalized g):SourceNormalizedDelocalized g:=by
  intro eig v heig hnorm i
  have hC:=sourceEigenvectorConstant_positive d hd
  have hNr:0<(N:ℝ):=Nat.cast_pos.mpr (by omega)
  have hlog:0≤Real.log (N:ℝ):=Real.log_nonneg (by exact_mod_cast hN)
  have hb:0≤Real.sqrt (sourceEigenvectorConstant d)*Real.log (N:ℝ)^150/Real.sqrt (N:ℝ):=by positivity
  have hsq:(Real.sqrt (sourceEigenvectorConstant d)*Real.log (N:ℝ)^150/Real.sqrt (N:ℝ))^2=
      sourceEigenvectorConstant d*(Real.log (N:ℝ)^300/(N:ℝ)):=by
    rw [div_pow,mul_pow,Real.sq_sqrt hC.le,Real.sq_sqrt hNr.le,←pow_mul]
    norm_num
    ring
  have hh:=hg eig v heig i
  rw [hnorm,mul_one] at hh
  rw [←hsq] at hh
  nlinarith [norm_nonneg (v i)]

theorem source_theorem_1_4_normalized (d:ℕ)(c β:ℝ)
    (hd:3≤d)(hc:0<c)(hc1:c<1)(hβ:0<β)(hβc:β≤c/32):
    ∀D:ℕ,∀ᶠ N:ℕ in Filter.atTop,Nonempty (LocalLaw.RegularGraph N d)→
      eventMass (LocalLaw.RegularGraph.weight (N:=N) (d:=d)) (fun g=>
        LocalLaw.RegularGraph.structural (logarithmicRadius (c/4) d N) (finiteOmega d) ⌊(N:ℝ)^c⌋₊ g ∧
          ¬SourceNormalizedDelocalized g)/
        eventMass (LocalLaw.RegularGraph.weight (N:=N) (d:=d))
          (LocalLaw.RegularGraph.structural (logarithmicRadius (c/4) d N) (finiteOmega d) ⌊(N:ℝ)^c⌋₊)≤
        1/(N:ℝ)^D:=by
  intro D
  filter_upwards [source_theorem_1_4_conditional d c β hd hc hc1 hβ hβc D,
    Filter.eventually_ge_atTop 1] with N hprob hN
  intro hnonempty
  have hnum:eventMass (LocalLaw.RegularGraph.weight (N:=N) (d:=d)) (fun g=>
      LocalLaw.RegularGraph.structural (logarithmicRadius (c/4) d N) (finiteOmega d) ⌊(N:ℝ)^c⌋₊ g ∧
        ¬SourceNormalizedDelocalized g)≤
      eventMass (LocalLaw.RegularGraph.weight (N:=N) (d:=d)) (fun g=>
        LocalLaw.RegularGraph.structural (logarithmicRadius (c/4) d N) (finiteOmega d) ⌊(N:ℝ)^c⌋₊ g ∧
          ¬SourceDelocalized g):=by
    apply eventMass_mono LocalLaw.RegularGraph.weight LocalLaw.RegularGraph.weight_nonnegative
    intro g hg
    exact ⟨hg.1,fun h=>hg.2 (sourceDelocalized_normalized g hd hN h)⟩
  have hden:0≤eventMass (LocalLaw.RegularGraph.weight (N:=N) (d:=d))
      (LocalLaw.RegularGraph.structural (logarithmicRadius (c/4) d N) (finiteOmega d) ⌊(N:ℝ)^c⌋₊):=by
    unfold eventMass
    exact Finset.sum_nonneg (fun g _=>by
      split_ifs
      · exact LocalLaw.RegularGraph.weight_nonnegative g
      · exact le_rfl)
  exact (div_le_div_of_nonneg_right hnum hden).trans (hprob hnonempty)

end SpectralConsequences
#print axioms SpectralConsequences.source_theorem_1_4_normalized
