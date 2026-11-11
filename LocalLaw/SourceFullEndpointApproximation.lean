import LocalLaw.OldFullEndpointGeometry
import LocalLaw.FullEndpointStability
import LocalLaw.FullEndpointSurgeryParameters
import LocalLaw.FullEndpointCardinality
import LocalLaw.SourceObservationGeneralCap

/-! # First-stage full modified-endpoint approximation from the source weak event

The new full benchmark's class follows from the old root-ball structure and
actual pendant tree geometry. No new weak event or new model-class condition
is assumed. Its genuine physical endpoint block approaches this benchmark
uniformly, including the original endpoint a=12, b=25a.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance sourceFullEndpointApproxDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph

theorem eventually_source_fullEndpoint_approximation (a b d : ℕ) (c β B τ : ℝ)
    (ha : 12 ≤ a) (hb : 25 * a ≤ b) (hd : 3 ≤ d) (hc : 0 < c)
    (hβ : 0 < β) (hβc : β ≤ c / 32) (hτ : 0 < τ) (hτone : τ ≤ 1) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0 < z.im → ‖z‖ ≤ B → Real.log (N : ℝ) ^ b / (N : ℝ) ≤ z.im → ∀ badCount : ℕ,
      g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c / 4) d N) (finiteOmega d) badCount z →
      ∀ {ι : Type} [Fintype ι]
      (boundary : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z - 1))),
      let T := graphBallVertices g.graph o (actualCavityDepth a d N z - 1)
      let selector := logarithmicRadius (c / 4) d N / 4
      let r := effectiveModelRadius a d N β
      let s := g.admissibleState T boundary samples
      let gnew := g.labelledResampledGraph T boundary samples selector
      let e := s.fullEndpointModelEmbedding selector r
      ∀ i j : s.fullEndpointRoots selector,
        ‖gnew.G z i.val j.val - (gnew.filledExteriorModel T (s.endpointModelVertices selector r)).extensionGreen
          (g.Q z) z (e i) (e j)‖ ≤ τ := by
  let A := filledEndpointLogCap d β
  let K := DeficientGraph.localizationWeakConstant d B A
  let D := 1 + K
  let D' := D / τ
  let U := fullEndpointCountConstant d
  let C0 := 2 * finiteExtraReferenceConstant d
  let w := 2 * (d : ℝ) / Real.sqrt ((d : ℝ) - 1)
  have hAobs := sourceObservationLogCap_nonnegative d hd β hβ.le
  have hA : 0 ≤ A := by dsimp only [A, filledEndpointLogCap]; linarith
  have hAle : sourceObservationLogCap d β ≤ A := by dsimp only [A, filledEndpointLogCap]; linarith
  have hK : 0 ≤ K := (by norm_num : (0 : ℝ) ≤ 1).trans
    (DeficientGraph.localizationWeakConstant_ge_one d hd B A hA)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hD' : 0 ≤ D' := div_nonneg hD hτ.le
  have hU : 0 ≤ U := by dsimp only [U, fullEndpointCountConstant]; positivity
  have hCextra : 0 ≤ finiteExtraReferenceConstant d := (by norm_num : (0 : ℝ) ≤ 1).trans
    (finiteExtraReferenceConstant_ge_one d hd)
  have hC0 : 0 ≤ C0 := by dsimp only [C0]; positivity
  have hw : 0 ≤ w := by dsimp only [w]; positivity
  have hdepth := (lowerLogLogRadius_tendsto a d (by omega) hd).eventually (Filter.eventually_ge_atTop 4)
  filter_upwards [eventually_sourceObservationBounds_of_cap a b d c β B 1 A ha hb hd hc hβ hβc le_rfl hAle,
    eventually_filledEndpoint_diameter_log a b d c β B 1 ha hb hd hc hβ hβc le_rfl,
    eventually_full_endpoint_surgery_budgets a b d β U C0 w D' ha hb hd hβ hU hC0 hw hD',
    eventually_effectiveModelRadius_margins a d c β (by omega) hd hc hβ hβc, hdepth]
    with N hnum hlog hcoarse hmarg hdepth
  intro g o z hz hzB hfloor badCount hsource ι _ boundary samples
  dsimp only
  let ell := actualCavityDepth a d N z - 1
  let R := logarithmicRadius (c / 4) d N
  let selector := R / 4
  let r := effectiveModelRadius a d N β
  let T := graphBallVertices g.graph o ell
  let s := g.admissibleState T boundary samples
  let gnew := g.labelledResampledGraph T boundary samples selector
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  let L := Real.log (N : ℝ)
  let n := Nat.card (s.fullEndpointRoots selector)
  let e := s.fullEndpointModelEmbedding selector r
  let Mnew := gnew.filledExteriorModel T (s.endpointModelVertices selector r)
  have num := hnum z hz hfloor
  have hL : 1 ≤ L := num.log_one
  have hε : 0 ≤ ε := num.error_nonnegative
  have hsep : 2 * r + 2 ≤ selector := by
    have hh := hmarg.2.2.2 z
    dsimp only [r, selector, R]
    omega
  have hmargin : ell + r + 1 ≤ R := by
    have hh := hmarg.2.2.2 z
    dsimp only [ell, r, R]
    omega
  have hstruct : graphBallExcess g.graph o R ≤ finiteOmega d := hsource.1.1 o
  have hOldClass := (g.old_filledEndpoint_component_budget o ell selector r R hsep hmargin hstruct boundary samples).to_componentFinite
  have hNewClass := (g.filledEndpoint_component_reference_budget o ell selector r R boundary samples hsep hmargin hstruct).to_componentFinite
  have hOldDiam := g.old_filledEndpoint_distance_bound o ell selector r R hsep hmargin hstruct boundary samples
  have hNewDiam := g.filledEndpoint_distance_bound o ell selector r R (finiteOmega d) boundary samples hsep hmargin hstruct
  have hRlog := hlog z hz hfloor
  have hcount : (n : ℝ) ≤ U * L ^ (2 * a) := g.fullEndpointRoots_card_log_bound o a ell selector hd hL
    (actualCavityDepth_radius_bounds a d N z hdepth).2 boundary samples
  have hnumeric := hcoarse z hz hfloor (n : ℝ) (Nat.cast_nonneg _) hcount
  have hprior : ‖g.Q z - semicircleRoot z‖ ≤ 1 * scalarScale (spectralScale z) ε := by
    simpa only [one_mul] using hsource.2.1
  have hweak : ∀ x y, ‖g.G z x y - g.P r z (g.Q z) x y‖ ≤ 1 * ε := by
    simpa only [one_mul] using hsource.2.2
  have hδD : fullEndpointSurgeryError d B 1 ε L A ≤ D * L * ε := by
    unfold fullEndpointSurgeryError
    simp only [one_pow, mul_one]
    exact mul_le_mul_of_nonneg_right (by dsimp only [D, K]; nlinarith only [hL]) hε
  have hDD' : D ≤ D' := (le_div_iff₀ hτ).mpr
    (by nlinarith only [mul_le_mul_of_nonneg_left hτone hD])
  have hδupper : fullEndpointSurgeryError d B 1 ε L A ≤ D' * L * ε :=
    hδD.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDD' (by linarith)) hε)
  have hsmall : (n : ℝ) * (1 + fullEndpointSurgeryRowCap d n * w) * w *
      fullEndpointSurgeryError d B 1 ε L A ≤ 1 / 2 := by
    exact (mul_le_mul_of_nonneg_left hδupper (by dsimp only [fullEndpointSurgeryRowCap]; positivity)).trans hnumeric.1
  have hbound := g.fullEndpoint_entry_stability_of_geometry hd T boundary samples selector r
    (filledEndpointDiameter d ell r) (g.Q z) z hz (g.Q_im_nonnegative z hz) B 1 ε L A hzB num
    hOldClass hNewClass hOldDiam hNewDiam hRlog (s.fullEndpoint_old_root_ball_capture selector r)
    hprior hweak hsmall
  have herror : 2 * (1 + fullEndpointSurgeryRowCap d n * w) ^ 2 *
      fullEndpointSurgeryError d B 1 ε L A ≤ τ := by
    have hδτ : fullEndpointSurgeryError d B 1 ε L A ≤ τ * (D' * L * ε) :=
      hδD.trans_eq (by dsimp only [D']; field_simp)
    calc
      _ ≤ 2 * (1 + fullEndpointSurgeryRowCap d n * w) ^ 2 * (τ * (D' * L * ε)) :=
        mul_le_mul_of_nonneg_left hδτ (by positivity)
      _ = τ * (2 * (1 + (n : ℝ) * C0 * w) ^ 2 * (D' * L * ε)) := by
        dsimp only [fullEndpointSurgeryRowCap, C0]
        ring
      _ ≤ τ * 1 := mul_le_mul_of_nonneg_left hnumeric.2 hτ.le
      _ = τ := mul_one _
  intro i j
  exact (hbound i j).trans herror

end RegularGraph
end LocalLaw
