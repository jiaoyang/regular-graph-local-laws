import SpectralConsequences.SourceCountingRate

/-! # The actual conditional ensemble counting law

Every positive polynomial failure rate follows from the completed uniform
source local law. The conditioning event is the same finite-core structural
event; no positivity of its mass is inserted as an unproved premise.
-/
open Filter
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance sourceCountingProbabilityDecidable (p:Prop):Decidable p:=Classical.propDecidable p

theorem source_counting_rate (d:ℕ) (a b c β:ℝ)
    (hd:3≤d) (ha:12≤a) (hb:25*a≤b) (hc:0<c) (hc1:c<1)
    (hβ:0<β) (hβc:β≤c/32):
    ∀D:ℕ,∀ᶠ N:ℕ in atTop,Nonempty (RegularGraph N d)→
      eventMass (RegularGraph.weight (N:=N) (d:=d)) (fun g=>
        RegularGraph.structural (logarithmicRadius (c/4) d N) (finiteOmega d) ⌊(N:ℝ)^c⌋₊ g∧
          ¬SourceCountingCDFGood β g)/
      eventMass (RegularGraph.weight (N:=N) (d:=d))
        (RegularGraph.structural (logarithmicRadius (c/4) d N) (finiteOmega d) ⌊(N:ℝ)^c⌋₊)≤
      1/(N:ℝ)^D := by
  intro D
  have hβsmall:β≤1/3:=by linarith
  filter_upwards [source_theorem_4_2 d a b c β hd ha hb hc hc1 hβ hβc D,
    eventually_source_local_law_implies_counting_rate d a b β (sourceUniformLawConstant d) hd hβ hβsmall]
    with N hlocal hcount
  intro hnonempty
  have hsub : ∀g:RegularGraph N d,
      (RegularGraph.structural (logarithmicRadius (c/4) d N) (finiteOmega d) ⌊(N:ℝ)^c⌋₊ g∧
        ¬SourceCountingCDFGood β g) →
      (RegularGraph.structural (logarithmicRadius (c/4) d N) (finiteOmega d) ⌊(N:ℝ)^c⌋₊ g∧
        ¬∀z:ℂ,0<z.im→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→
          RealSourceLocalLawAt (by omega) a (logarithmicRadius β d N) (sourceUniformLawConstant d) z g) := by
    intro g hg
    exact ⟨hg.1,fun h=>hg.2 (hcount g h)⟩
  have hmass:=eventMass_mono (RegularGraph.weight (N:=N) (d:=d)) RegularGraph.weight_nonnegative hsub
  have hden:0≤eventMass (RegularGraph.weight (N:=N) (d:=d))
      (RegularGraph.structural (logarithmicRadius (c/4) d N) (finiteOmega d) ⌊(N:ℝ)^c⌋₊):=by
    unfold eventMass
    apply Finset.sum_nonneg
    intro g _
    split_ifs
    · exact RegularGraph.weight_nonnegative g
    · exact le_rfl
  exact (div_le_div_of_nonneg_right hmass hden).trans (hlocal hnonempty)

end SpectralConsequences
