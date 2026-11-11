import SpectralConsequences.SourceMomentGeometricExit
import SpectralConsequences.SourceWeakProbability

/-! The literal work event and its auxiliary count events in Section7. -/
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance sourceMomentEventsDecidable (p:Prop):Decidable p:=Classical.propDecidable p

def momentSourceEvent (N d a:ℕ) (c β:ℝ) (z:ℂ) (g:RegularGraph N d):Prop:=
  g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
    (logarithmicRadius (c/4) d N) (finiteOmega d) ⌊(N:ℝ)^c⌋₊ z

def momentTreeEvent (N d:ℕ) (o:Fin N) (c:ℝ) (g:RegularGraph N d):Prop:=
  (graphBall g.graph o (logarithmicRadius (c/4) d N)).IsTree

def momentAuxiliary (N d:ℕ) (c:ℝ) (g:RegularGraph N d):Prop:=
  LargeTreeCountAux (4*c) (7*c) g ∧ WorkTreeCountAux (4*c) (7*c/8) g

def momentWeakFailure (N d a:ℕ) (c β:ℝ) (z:ℂ) (g:RegularGraph N d):Prop:=
  RegularGraph.structural (logarithmicRadius (c/4) d N) (finiteOmega d) ⌊(N:ℝ)^c⌋₊ g ∧
    ¬momentSourceEvent N d a c β z g

theorem eventually_moment_auxiliary_failure (d D:ℕ) (c:ℝ) (hd:3≤d) (hc:0<c):
    ∀ᶠ N:ℕ in Filter.atTop,
      eventMass (RegularGraph.weight (N:=N) (d:=d)) (fun g=>¬momentAuxiliary N d c g)≤2/(N:ℝ)^D:=by
  filter_upwards [eventually_largeTreeCountAux_failure d D (4*c) (7*c) hd (by positivity) (by linarith),
    eventually_workTreeCountAux_failure d D (4*c) (7*c/8) hd (by positivity) (by linarith)]
    with N hLarge hWork
  have hcover:∀g:RegularGraph N d,¬momentAuxiliary N d c g→
      ¬LargeTreeCountAux (4*c) (7*c) g ∨ ¬WorkTreeCountAux (4*c) (7*c/8) g:=by
    intro g hg
    exact not_and_or.mp hg
  apply (eventMass_mono RegularGraph.weight RegularGraph.weight_nonnegative hcover).trans
  apply (eventMass_union_le RegularGraph.weight RegularGraph.weight_nonnegative _ _).trans
  exact (add_le_add hLarge hWork).trans_eq (by ring)

theorem moment_exit_cover (N d a:ℕ) (c β:ℝ) (z:ℂ) (o:Fin N) (g:RegularGraph N d):
    ¬(momentSourceEvent N d a c β z g∧momentTreeEvent N d o c g)↔
      (¬RegularGraph.structural (logarithmicRadius (c/4) d N) (finiteOmega d) ⌊(N:ℝ)^c⌋₊ g ∨
        ¬momentTreeEvent N d o c g) ∨ momentWeakFailure N d a c β z g:=by
  constructor
  · intro hnot
    by_cases hs:RegularGraph.structural (logarithmicRadius (c/4) d N) (finiteOmega d) ⌊(N:ℝ)^c⌋₊ g
    · by_cases ht:momentTreeEvent N d o c g
      · exact Or.inr ⟨hs,fun hΩ=>hnot ⟨hΩ,ht⟩⟩
      · exact Or.inl (Or.inr ht)
    · exact Or.inl (Or.inl hs)
  · rintro (⟨hs | ht⟩ | hw) ⟨hΩ,hT⟩
    · exact hs hΩ.1
    · exact ht hT
    · exact hw.2 hΩ

end SpectralConsequences
