import LocalLaw.SourceOutsideRowReduction
import LocalLaw.SourceOutsideModelColumns

/-! # Actual outside-row conclusion from one named column good event

Every finite-class, diameter, capture, model-column and normalization input
is discharged for the actual switched one-target model.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2400000
namespace LocalLaw
local instance sourceOutsideRowFromColumnDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def sourceOutsideRowBaseConstant (d J : ℕ) (β C1 Eout : ℝ) : ℝ :=
  sourceOutsideReductionBase d J β C1 Eout (sourceOutsideModelColumnConstant d)

def sourceOutsideRowFeedbackConstant (d : ℕ) (β B : ℝ) : ℝ :=
  sourceOutsideReductionFeedback d β B (singleTargetFilledLogCap d β) (sourceOutsideModelColumnConstant d)

namespace RegularGraph
variable {N d : ℕ}

def SourceOutsideColumnGood (g : RegularGraph N d) (a : ℕ) (c β Eout : ℝ) (o : Fin N) (z : ℂ)
    {ι : Type} [Fintype ι]
    (labels : ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
    (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))) : Prop :=
  let ell := actualCavityDepth a d N z-1
  let r := effectiveModelRadius a d N β
  let R := logarithmicRadius (c/4) d N
  let T := graphBallVertices g.graph o ell
  let gnew := g.labelledResampledGraph T labels samples (R/4)
  let L := Real.log (N:ℝ)
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  ∀ (y : Fin N) (hy : y∉T),
  let K := g.singleTargetOutsideVertices T labels samples (R/4) r y
  let hK := g.singleTargetOutside_boundary_capture T labels samples (R/4) r y
  let j := g.singleTargetOutsideTargetVertex T labels samples (R/4) r y hy
  ∑ α : BoundaryOrientedEdge gnew.graph T,
    ‖(gnew.deficient.delete T).G z (boundaryOutsideVertex gnew.graph T α) j.val-
      ((gnew.deficient.delete T).restrict K).extensionGreen (gnew.Q z) z
        (gnew.filledBoundaryVertex T K hK α) j‖≤Eout*L^5*ε

theorem eventually_source_outside_row_from_column (a b d J : ℕ) (c β B C1 Eout : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c) (hβ : 0<β)
    (hβc : β≤c/32) (hC1 : 1≤C1) (hB : 0≤B) (hEout : 0≤Eout) :
    ∀ᶠ N : ℕ in Filter.atTop,∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0<z.im → ‖z‖≤B → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → ∀ Cq badCount : ℕ,
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1)
        (finiteOmega d) Cq badCount C1 o z → ∀ {ι : Type} [Fintype ι]
      (labels : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let ell := actualCavityDepth a d N z-1
      let r := effectiveModelRadius a d N β
      let R := logarithmicRadius (c/4) d N
      let T := graphBallVertices g.graph o ell
      let L := Real.log (N:ℝ)
      let ε := graphPaperError a d N (logarithmicRadius β d N) z
      let φ := correlationThreshold L a N z.im (graphKestenMcKayReference d z).im (spectralScale z) ε
      let gnew := g.labelledResampledGraph T labels samples (R/4)
      gnew.SourceOmegaWithRadii a r (logarithmicRadius β d N) R (finiteOmega d) badCount z →
      ¬g.sourceGreenIsolationBad T z φ (R/4) (Nat.ceil L) samples →
      (rejectedResamplingIndices g.graph T (R/4) samples).card≤J →
      g.SourceOutsideColumnGood a c β Eout o z labels samples → ∀ y∉T,
      ‖gnew.G z o y-gnew.P r z (gnew.Q z) o y‖≤
        sourceOutsideRowBaseConstant d J β C1 Eout*ε/L+
          sourceOutsideRowFeedbackConstant d β B*L^2*gnew.sourceFeedback z := by
  let A := singleTargetFilledLogCap d β
  let S := sourceOutsideModelColumnConstant d
  have hC : 0≤finiteExtraReferenceConstant d := (by norm_num : (0:ℝ)≤1).trans (finiteExtraReferenceConstant_ge_one d hd)
  have hA : sourceObservationLogCap d β≤A := by
    have hh := sourceObservationLogCap_nonnegative d hd β hβ.le
    dsimp only [A,singleTargetFilledLogCap,filledEndpointLogCap]
    linarith
  have hS : 0≤S := by dsimp only [S,sourceOutsideModelColumnConstant]; positivity
  filter_upwards [eventually_source_outside_row_of_boundary_column a b d J c β B C1 A Eout S
      ha hb hd hc hβ hβc hC1 hB hA hEout hS,
    eventually_singleTargetFilled_geometry a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_source_outside_model_column a b d c β B C1 ha hb hd hc hβ hβc hC1]
    with N hrow hgeom hmodel
  intro g o z hz hzB hfloor Cq badCount hplus ι _ labels samples
  dsimp only
  let ell := actualCavityDepth a d N z-1
  let r := effectiveModelRadius a d N β
  let T := graphBallVertices g.graph o ell
  let R := logarithmicRadius (c/4) d N
  let gnew := g.labelledResampledGraph T labels samples (R/4)
  intro htarget hisolation hrejected hcolumn y hy
  let K := g.singleTargetOutsideVertices T labels samples (R/4) r y
  let hK := g.singleTargetOutside_boundary_capture T labels samples (R/4) r y
  let j := g.singleTargetOutsideTargetVertex T labels samples (R/4) r y hy
  let Rmodel := singleTargetFilledDiameter d ell r
  have geom := g.singleTargetOutside_geometry T labels samples (R/4) r y Rmodel A (Real.log (N:ℝ))
    (hgeom g o z hz hfloor Cq badCount hplus labels samples htarget y)
  have hcinner (x : T) : graphBallVertices gnew.graph x.val r⊆filledExteriorVertices T K := fun v hv =>
    g.singleTargetOutside_inner_capture T labels samples (R/4) r y x
      (graphBallVertices_mono gnew.graph x.val (Nat.le_succ r) hv)
  have hcj : graphBallVertices gnew.graph j.val.val r⊆filledExteriorVertices T K := by
    rw [g.singleTargetOutside_fill_eq]
    exact fun v hv => Or.inr (Or.inl hv)
  have hcol : ∑ α : BoundaryOrientedEdge gnew.graph T,
      ‖(gnew.deficient.delete T).G z (boundaryOutsideVertex gnew.graph T α) j.val-
        ((gnew.deficient.delete T).restrict K).extensionGreen (gnew.Q z) z (gnew.filledBoundaryVertex T K hK α) j‖≤
      Eout*Real.log (N:ℝ)^5*graphPaperError a d N (logarithmicRadius β d N) z := hcolumn y hy
  exact hrow g o z hz hzB hfloor Cq badCount hplus labels samples htarget hisolation hrejected K Rmodel hK
    geom.finite_budget geom.diameter geom.diameter_log hcinner j hcj hcol
      (hmodel g o z hz hfloor Cq badCount hplus labels samples htarget y hy).2

end RegularGraph
end LocalLaw
