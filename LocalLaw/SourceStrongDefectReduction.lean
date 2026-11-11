import LocalLaw.SourceSecondStageProbability
import LocalLaw.StrongReversibleDefect
import LocalLaw.GraphResamplingDefect

/-! # The actual local defect needs only the first resampling-stage estimate

The strong closure budget, exceptional averaging, all target-restricted
second-stage estimates and the actual reversible kernel are instantiated.
This intermediate reduction takes the first-stage probability as an explicit
hypothesis; `SourceFirstStageProof` proves that estimate.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance sourceStrongDefectReductionDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem eventually_source_strong_defect_reduction (a b d p Cq : ℕ) (c β γ B C1 : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hc : 0 < c) (hc₁ : c < 1)
    (hβ : 0 < β) (hβc : β ≤ c / 32) (hγ : c / 4 < γ) (hgap : γ + β < 1)
    (hB : 0 ≤ B) (hC1 : 1 ≤ C1) (hCdel : sourceDeletionConstant d β B ≤ C1)
    (hCq : finiteOmega d ≤ Cq) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ z : ℂ, 0 < z.im → ‖z‖ ≤ B →
      Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im → ∀ α : Fin N → ℝ,
      let R := logarithmicRadius (c / 4) d N
      let rn := logarithmicRadius β d N
      let r := effectiveModelRadius a d N β
      let ell := actualCavityDepth a d N z - 1
      let A : RegularGraph N d → Prop := RegularGraph.offsetStructural R (finiteOmega d) 1 ⌊(N : ℝ) ^ γ⌋₊
      let F := graphLocalLawFamilyWithRadii N d a r rn
      (∀ o : Fin N,
        eventMass (ballLabelledWeight N d o ell) (fun ξ =>
          (A (ballLabelledProject ξ) ∧ F.weak z (ballLabelledProject ξ)) ∧
          ¬(ballLabelledProject (ballLabelledResample N d (R / 4) ξ)).SourceOmegaPlusWithRadii
            a r rn R ell (finiteOmega d) Cq ⌊(N : ℝ) ^ γ⌋₊ C1 o z) ≤ α o) →
      eventMass (RegularGraph.weight (N := N) (d := d)) (fun g =>
        A g ∧ F.weak z g ∧ ¬F.strict z g) ≤ ∑ o : Fin N, (α o + 8 / (N : ℝ) ^ p) := by
  obtain ⟨qReject, qGeo, _, _, hsecond⟩ :=
    eventually_actual_second_stage_strong_certificate_probability a b d p Cq c β γ B C1
      ha hb hd hc hc₁ hβ hβc hγ hgap hB hC1 hCdel hCq
  let U := sourceSecondU d Cq qReject qGeo β B C1
  let V := sourceSecondV d β B
  let M0 := sourceSecondM d Cq qReject β C1
  have hU : 0 ≤ U := by unfold U sourceSecondU sourceStrongRowU; positivity
  have hV : 0 ≤ V := by unfold V sourceSecondV sourceStrongRowV; positivity
  have hM0 : 0 < M0 := by unfold M0 sourceSecondM sourceStrongResidualM; positivity
  filter_upwards [hsecond,
    eventually_strong_source_closure_inputs a b d c β γ B U V M0 ha hb hd hc hβ hβc hgap hB hU hV hM0,
    eventually_selected_resampling_budget a d hd (by omega), Filter.eventually_ge_atTop 1]
    with N hsecond hclosure hbudget hN
  intro z hz hzB hfloor α
  dsimp only
  let R := logarithmicRadius (c / 4) d N
  let rn := logarithmicRadius β d N
  let r := effectiveModelRadius a d N β
  let ell := actualCavityDepth a d N z - 1
  let ε := graphPaperError a d N rn z
  let A : RegularGraph N d → Prop := RegularGraph.offsetStructural R (finiteOmega d) 1 ⌊(N : ℝ) ^ γ⌋₊
  let F := graphLocalLawFamilyWithRadii N d a r rn
  let Bsite := fun o (g : RegularGraph N d) =>
    g.SourceOmegaPlusWithRadii a r rn R ell (finiteOmega d) Cq ⌊(N : ℝ) ^ γ⌋₊ C1 o z
  intro hfirst
  obtain ⟨D, hdepth, hL, hDU, hDV, hDM, hbase, hfeedback, hcavity, _, habsorb⟩ := hclosure z hz hzB hfloor
  have hbase' : D.rowBase = D.U * ε / D.L := by simpa only [hDU, hL] using hbase
  have hfeedback' : D.rowFeedback = D.V * D.L ^ 2 := by simpa only [hDV, hL] using hfeedback
  have hcavity' : D.cavityError = D.residualConstant * ε / (2 * D.L ^ 4) := by
    simpa only [hDM, hL] using hcavity
  apply actual_strong_graph_resampling_defect_restricted N d a r rn R ell (R / 4) z
    (by omega) (by omega) (hbudget z) A D Bsite α (fun _ => 8 / (N : ℝ) ^ p)
  · intro g hg hw
    exact (habsorb g hg hw).1
  · intro g hg hw
    exact (habsorb g hg hw).2
  · exact hfirst
  · intro o
    have hs := hsecond o z hz hzB hfloor D hdepth hL hDU hDV hDM hbase' hfeedback' hcavity'
    apply (eventMass_mono (ballLabelledWeight N d o ell) (ballLabelledWeight_nonnegative N d o ell) ?_).trans hs
    intro ξ hξ
    exact ⟨hξ.1, ⟨RegularGraph.offsetStructural_implies_structural hξ.2.1.1, hξ.2.1.2⟩, hξ.2.2⟩

end LocalLaw
