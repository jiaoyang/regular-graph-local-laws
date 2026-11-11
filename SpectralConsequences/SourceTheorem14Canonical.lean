import SpectralConsequences.SourceDelocalizationSupnorm

/-! The full graph delocalization conclusions with no auxiliary exponent
in their public hypotheses. All eigenspaces and all vectors are covered. -/
noncomputable section
namespace SpectralConsequences
open LocalLaw

theorem source_theorem_1_4 (d:ℕ)(c:ℝ)(hd:3≤d)(hc:0<c)(hc1:c<1):
    ∀D:ℕ,∀ᶠ N:ℕ in Filter.atTop,Nonempty (RegularGraph N d)→
      eventMass (RegularGraph.weight (N:=N) (d:=d)) (fun g=>
        RegularGraph.structural (logarithmicRadius (c/4) d N) (finiteOmega d) ⌊(N:ℝ)^c⌋₊ g ∧
          ¬SourceDelocalized g)/
        eventMass (RegularGraph.weight (N:=N) (d:=d))
          (RegularGraph.structural (logarithmicRadius (c/4) d N) (finiteOmega d) ⌊(N:ℝ)^c⌋₊)≤1/(N:ℝ)^D:=
  source_theorem_1_4_conditional d c (c/64) hd hc hc1 (by positivity) (by linarith)

theorem source_theorem_1_4_supnorm (d:ℕ)(c:ℝ)(hd:3≤d)(hc:0<c)(hc1:c<1):
    ∀D:ℕ,∀ᶠ N:ℕ in Filter.atTop,Nonempty (RegularGraph N d)→
      eventMass (RegularGraph.weight (N:=N) (d:=d)) (fun g=>
        RegularGraph.structural (logarithmicRadius (c/4) d N) (finiteOmega d) ⌊(N:ℝ)^c⌋₊ g ∧
          ¬SourceNormalizedDelocalized g)/
        eventMass (RegularGraph.weight (N:=N) (d:=d))
          (RegularGraph.structural (logarithmicRadius (c/4) d N) (finiteOmega d) ⌊(N:ℝ)^c⌋₊)≤1/(N:ℝ)^D:=
  source_theorem_1_4_normalized d c (c/64) hd hc hc1 (by positivity) (by linarith)

end SpectralConsequences
#print axioms SpectralConsequences.source_theorem_1_4
#print axioms SpectralConsequences.source_theorem_1_4_supnorm
