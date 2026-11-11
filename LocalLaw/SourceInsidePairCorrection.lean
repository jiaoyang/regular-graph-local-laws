import LocalLaw.SourceFilledEndpointBudget
import LocalLaw.FilledReferencePairComparison
import LocalLaw.ActualSwitchingQChange

/-! # Actual fixed-reference to switched pair-model correction for inside rows -/

noncomputable section
namespace LocalLaw
local instance sourceInsidePairCorrectionDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem constant_div_log_absorption (p q : ℕ) (L ε K : ℝ)
    (hL : 1≤L) (hε : 0≤ε) (hK : K≤L) (hpq : q+1≤p) :
    K*ε/L^p≤ε/L^q := by
  have hLp : 0<L := by linarith
  calc
    _ ≤ L*ε/L^p := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hK hε) (pow_nonneg hLp.le _)
    _ = L*(ε/L^p) := by ring
    _ ≤ L*(ε/L^(q+1)) := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left hε (pow_pos hLp _) (pow_le_pow_right₀ hL hpq)) hLp.le
    _ = ε/L^q := by rw [pow_succ]; field_simp; ring

def sourceInsidePairFeedbackConstant (d : ℕ) (β B : ℝ) : ℝ :=
  DeficientGraph.localizationFeedbackConstant d B (filledEndpointLogCap d β)

namespace RegularGraph

theorem eventually_source_inside_pair_correction (a b d : ℕ) (c β B C1 : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c)
    (hβ : 0<β) (hβc : β≤c/32) (hC1 : 1≤C1) (hB : 0≤B) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0<z.im → ‖z‖≤B → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → ∀ Cq badCount : ℕ,
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1)
        (finiteOmega d) Cq badCount C1 o z →
      ∀ {ι : Type} [Fintype ι]
      (labels : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let ell := actualCavityDepth a d N z-1
      let R := logarithmicRadius (c/4) d N
      let r := effectiveModelRadius a d N β
      let T := graphBallVertices g.graph o ell
      let L := Real.log (N:ℝ)
      let ε := graphPaperError a d N (logarithmicRadius β d N) z
      let gnew := g.labelledResampledGraph T labels samples (R/4)
      gnew.SourceOmegaWithRadii a r (logarithmicRadius β d N) R (finiteOmega d) badCount z →
      ∀ x y : T,
      ‖g.sourceRetainedReference T r (g.Q z) z x y-gnew.P r z (gnew.Q z) x.val y.val‖≤
        2*(ε/L^2)+sourceInsidePairFeedbackConstant d β B*L*gnew.sourceFeedback z := by
  let A := filledEndpointLogCap d β
  let C := finiteExtraReferenceConstant d
  let κ : ℝ := ((d-1:ℕ):ℝ)^4
  let Kcont := 16*C^2*A
  let Ktail := DeficientGraph.localizationTailConstant d*κ
  have hAobs := sourceObservationLogCap_nonnegative d hd β hβ.le
  have hA : 0≤A := by dsimp only [A,filledEndpointLogCap]; linarith
  have hAcompare : sourceObservationLogCap d β≤A := by dsimp only [A,filledEndpointLogCap]; linarith
  have hC : 0≤C := (by norm_num : (0:ℝ)≤1).trans (finiteExtraReferenceConstant_ge_one d hd)
  have hκ : 0≤κ := by dsimp only [κ]; positivity
  have hdR : (3:ℝ)≤d := Nat.cast_le.mpr hd
  have hk : 0<(d:ℝ)-1 := by linarith
  have hTail : 0≤DeficientGraph.localizationTailConstant d := by
    unfold DeficientGraph.localizationTailConstant DeficientGraph.localizationExceptionalMass
    positivity
  have hC10 : 0≤C1 := (by norm_num : (0:ℝ)≤1).trans hC1
  filter_upwards [eventually_source_fullEndpoint_geometry a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_sourceObservationBounds a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_actual_switching_Q_change a b d c β B C1 ha hb hd hc hβ hβc hC10 hB,
    eventually_effectiveModelRadius_margins a d c β (by omega) hd hc hβ hβc,
    eventually_log_ge_nat (DeficientGraph.localizationBudgetConstant d B A),
    eventually_log_ge_nat Kcont,eventually_log_ge_nat Ktail]
    with N hgeometry hnum hchange hmargins hlarge hcontLarge htailLarge
  intro g o z hz hzB hfloor Cq badCount hplus ι _ labels samples
  dsimp only
  let ell := actualCavityDepth a d N z-1
  let R := logarithmicRadius (c/4) d N
  let r := effectiveModelRadius a d N β
  let T := graphBallVertices g.graph o ell
  let L := Real.log (N:ℝ)
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  let εs := C1^2*ε
  let gnew := g.labelledResampledGraph T labels samples (R/4)
  let Rfull := filledEndpointDiameter d ell r
  intro htarget x y
  have num := hnum z hz hfloor
  have geo := hgeometry g o z hz hfloor Cq badCount hplus labels samples
  have hL : 1≤L := num.log_one
  have hLp : 0<L := by linarith
  have hε : 0≤ε := num.error_nonnegative
  have hεs : 0≤εs := mul_nonneg (sq_nonneg C1) hε
  have hscaled : εs*L^4≤1 := num.error_scaled
  have hεsOne : εs≤1 := by
    calc
      _ = εs*1 := (mul_one _).symm
      _ ≤ εs*L^4 := mul_le_mul_of_nonneg_left (one_le_pow₀ hL) hεs
      _ ≤ _ := hscaled
  have habs := scalarScale_constant_absorption (spectralScale z) ε C1 (spectralScale_pos hz) hε hC1
  have hpriorOld : ‖g.Q z-semicircleRoot z‖≤scalarScale (spectralScale z) εs := hplus.cavity.trans habs
  have hweakNew : ‖gnew.Q z-semicircleRoot z‖≤scalarScale (spectralScale z) ε := htarget.2.1
  have hpriorNew : ‖gnew.Q z-semicircleRoot z‖≤scalarScale (spectralScale z) εs :=
    hweakNew.trans ((le_mul_of_one_le_left (scalarScale_nonneg hε) hC1).trans habs)
  have hpairLog : ((4*r+1:ℕ)+1:ℝ)≤A*L :=
    num.pair_log.trans (mul_le_mul_of_nonneg_right hAcompare hLp.le)
  have hsep : 2*r+2≤R/4 := by have hh := hmargins.2.2.2 z; dsimp only [r,R]; omega
  have hrs : r+2≤R/4 := by have hh := hmargins.2.2.2 z; dsimp only [r,R]; omega
  have hcmp := g.filledReference_pair_comparison hd T labels samples (R/4) r hsep hrs
    (g.Q z) (gnew.Q z) z hz (g.Q_im_nonnegative z hz) (gnew.Q_im_nonnegative z hz)
    B εs L A hzB hεs hεsOne hL hA hscaled hpriorOld hpriorNew Rfull geo.finite_budget geo.diameter
    geo.diameter_log hpairLog hlarge x y
  have hQ := hchange g o z hz hzB hfloor Cq badCount hplus labels samples htarget
  have hcont : 16*C^2*((Rfull:ℝ)+1)*‖g.Q z-gnew.Q z‖≤Kcont*L*(ε/L^16) := by
    calc
      _ ≤ (16*C^2*(A*L))*(ε/L^16) := mul_le_mul
        (mul_le_mul_of_nonneg_left geo.diameter_log (by positivity)) hQ (norm_nonneg _) (by positivity)
      _ = _ := by dsimp only [Kcont]; ring
  have hcontAbs : Kcont*L*(ε/L^16)≤ε/L^2 := by
    calc
      _ = Kcont*ε/L^15 := by field_simp; ring
      _ ≤ _ := constant_div_log_absorption 15 2 L ε Kcont hL hε hcontLarge (by omega)
  have htail := effectiveModelRadius_localization_tail a d N β hd hL hmargins.1 z hz.le
  have htailAbs : DeficientGraph.localizationTailConstant d*physicalTransfer d z^(2*r)≤ε/L^2 := by
    calc
      _ ≤ DeficientGraph.localizationTailConstant d*(κ*ε/L^(4*a)) :=
        mul_le_mul_of_nonneg_left htail hTail
      _ = Ktail*ε/L^(4*a) := by dsimp only [Ktail]; ring
      _ ≤ _ := constant_div_log_absorption (4*a) 2 L ε Ktail hL hε htailLarge (by omega)
  apply hcmp.trans
  change 16*C^2*((Rfull:ℝ)+1)*‖g.Q z-gnew.Q z‖+
    DeficientGraph.localizationFeedbackConstant d B A*L*gnew.sourceFeedback z+
    DeficientGraph.localizationTailConstant d*physicalTransfer d z^(2*r)≤_
  change _≤2*(ε/L^2)+DeficientGraph.localizationFeedbackConstant d B A*L*gnew.sourceFeedback z
  nlinarith only [hcont.trans hcontAbs,htailAbs]

end RegularGraph
end LocalLaw
