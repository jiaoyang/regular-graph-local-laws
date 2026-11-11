import LocalLaw.SourceCavityCaps
import LocalLaw.OffsetStructuralEvent

/-!
# Construct the source scalar-closure inputs from actual weak events

The exceptional cavity bound and its sparse averaging contribution are proved
from the physical weak event and the offset structural count. This constructs
the actual closure budget with those two formerly explicit hypotheses fully
discharged; the local row/cavity certificates remain separate resampling work.
-/

open scoped BigOperators
namespace LocalLaw
noncomputable section
local instance sourceClosureInputsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The source closure budget, including actual exceptional-value control
and its numerical absorption, exists uniformly for all sufficiently large N. -/
theorem eventually_source_closure_inputs (a b d : ℕ) (c β γ B U V : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hc : 0 < c)
    (hβ : 0 < β) (hβc : β ≤ c / 32) (hγβ : γ + β ≤ 1)
    (hB : 0 ≤ B) (hU : 0 ≤ U) (hV : 0 ≤ V) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ z : ℂ, 0 < z.im → ‖z‖ ≤ B →
      Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im →
      ∃ D : ClosureBudget z (semicircleRoot z) (spectralScale z)
          (graphPaperError a d N (logarithmicRadius β d N) z),
        D.depth = actualCavityDepth a d N z ∧ D.L = Real.log (N : ℝ) ∧
        D.rowBase = U * graphPaperError a d N (logarithmicRadius β d N) z / Real.log (N : ℝ) ∧
        D.rowFeedback = V * Real.log (N : ℝ) ∧
        D.cavityError = graphPaperError a d N (logarithmicRadius β d N) z /
          (2 * Real.log (N : ℝ) ^ 2) ∧ D.exceptionalCavity = sourceExceptionalCavityCap d B ∧
        ∀ g : RegularGraph N d,
          RegularGraph.offsetStructural (logarithmicRadius (c / 4) d N) (finiteOmega d) 1 ⌊(N : ℝ) ^ γ⌋₊ g →
          (graphLocalLawFamily N d a (logarithmicRadius β d N)).weak z g →
          (∀ i ∈ nonTreeCenters g.graph (logarithmicRadius (c / 4) d N),
            ‖cavityAtVertex g.graph d z i - cavityIterate z (g.Q z) D.depth‖ ≤ D.exceptionalCavity) ∧
          D.cavityError + (((nonTreeCenters g.graph (logarithmicRadius (c / 4) d N)).card : ℝ) / (N : ℝ)) *
              D.exceptionalCavity ≤ graphPaperError a d N (logarithmicRadius β d N) z / D.L ^ 2 := by
  let M := sourceExceptionalCavityCap d B
  have hM : 0 ≤ M := sourceExceptionalCavityCap_nonnegative d hd B hB
  filter_upwards [eventually_actual_closure_budget a b d β B U V M ha hb hd hβ hU hV,
    RegularGraph.eventually_sourceOmega_exceptional_cavity_cap a b d c β B ha hb hd hc hβ hβc hB,
    eventually_sparse_cavity_absorption a d β γ M (by omega) hd hβ.le hγβ hM]
    with N hbudget hcaps habsorb
  intro z hz hzB hscale
  obtain ⟨D, hdepth, hlog, hrow, hfeedback, hcavity, hexceptional⟩ := hbudget z hz hscale hzB
  refine ⟨D, hdepth, hlog, hrow, hfeedback, hcavity, hexceptional, ?_⟩
  intro g haux hweak
  have hstruct := RegularGraph.offsetStructural_implies_structural haux
  have hOmega : g.SourceOmega a (logarithmicRadius β d N) (logarithmicRadius (c / 4) d N)
      (finiteOmega d) ⌊(N : ℝ) ^ γ⌋₊ z := ⟨hstruct, hweak⟩
  have hbad : ((nonTreeCenters g.graph (logarithmicRadius (c / 4) d N)).card : ℝ) ≤ (N : ℝ) ^ γ :=
    (Nat.cast_le.mpr hstruct.2).trans (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) γ))
  constructor
  · intro i _
    rw [hdepth, hexceptional]
    exact hcaps g z _ hz hzB hscale hOmega i
  · rw [hcavity, hexceptional, hlog]
    have hs := habsorb _ hbad z hz.le
    calc
      _ ≤ graphPaperError a d N (logarithmicRadius β d N) z / (2 * Real.log (N : ℝ) ^ 2) +
          graphPaperError a d N (logarithmicRadius β d N) z / (2 * Real.log (N : ℝ) ^ 2) :=
        add_le_add_left hs _
      _ = _ := by ring

end
end LocalLaw
