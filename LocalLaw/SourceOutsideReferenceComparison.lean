import LocalLaw.SourceInsidePairCorrection
import LocalLaw.FilledBoundarySchur

/-! # Fixed retained reference versus any actual enlarged switched model

The comparison takes only finite class, diameter, and ball containment for
the enlarged model. Its analytic feedback, Q transport, and nominal tail
budgets are derived from the actual source and retained target events.
-/

noncomputable section
set_option maxHeartbeats 1200000
namespace LocalLaw
local instance sourceOutsideReferenceComparisonDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph

theorem eventually_source_enlarged_retained_comparison (a b d : ℕ) (c β B C1 A : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c) (hβ : 0<β)
    (hβc : β≤c/32) (hC1 : 1≤C1) (hB : 0≤B) (hA : sourceObservationLogCap d β≤A) :
    ∀ᶠ N : ℕ in Filter.atTop,∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0<z.im → ‖z‖≤B → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → ∀ Cq badCount : ℕ,
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1)
        (finiteOmega d) Cq badCount C1 o z → ∀ {ι : Type} [Fintype ι]
      (labels : ι ≃ BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let ell := actualCavityDepth a d N z-1
      let r := effectiveModelRadius a d N β
      let Rstruct := logarithmicRadius (c/4) d N
      let T := graphBallVertices g.graph o ell
      let L := Real.log (N:ℝ)
      let ε := graphPaperError a d N (logarithmicRadius β d N) z
      let gnew := g.labelledResampledGraph T labels samples (Rstruct/4)
      gnew.SourceOmegaWithRadii a r (logarithmicRadius β d N) Rstruct (finiteOmega d) badCount z →
      ∀ (K : Set (Tᶜ:Set (Fin N))) (Rmodel : ℕ),
      (gnew.filledExteriorModel T K).ComponentFiniteReferenceBudget →
      (∀ u v,(gnew.filledExteriorModel T K).graph.dist u v≤Rmodel) →
      (Rmodel:ℝ)+1≤A*L →
      (∀ x : T,graphBallVertices gnew.graph x.val r⊆filledExteriorVertices T K) →
      ∀ x y : T,
      ‖g.sourceRetainedReference T r (g.Q z) z x y-gnew.filledRetainedGreen T K (gnew.Q z) z x y‖≤
        3*(ε/L^2)+(sourceInsidePairFeedbackConstant d β B+
          DeficientGraph.localizationFeedbackConstant d B A)*L*gnew.sourceFeedback z := by
  let κ : ℝ := ((d-1:ℕ):ℝ)^4
  let Ktail := DeficientGraph.localizationTailConstant d*κ
  have hA0 : 0≤A := (sourceObservationLogCap_nonnegative d hd β hβ.le).trans hA
  have hC : 0≤finiteExtraReferenceConstant d := (by norm_num : (0:ℝ)≤1).trans (finiteExtraReferenceConstant_ge_one d hd)
  have hTail : 0≤DeficientGraph.localizationTailConstant d := by
    unfold DeficientGraph.localizationTailConstant DeficientGraph.localizationExceptionalMass
    have hh : 0<(d:ℝ)-1 := by have hdR : (3:ℝ)≤d := Nat.cast_le.mpr hd; linarith
    positivity
  filter_upwards [eventually_source_inside_pair_correction a b d c β B C1 ha hb hd hc hβ hβc hC1 hB,
    eventually_sourceObservationBounds a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_effectiveModelRadius_margins a d c β (by omega) hd hc hβ hβc,
    eventually_log_ge_nat (DeficientGraph.localizationBudgetConstant d B A),
    eventually_log_ge_nat Ktail] with N hfixed hnum hmargin hlarge htailLarge
  intro g o z hz hzB hfloor Cq badCount hplus ι _ labels samples
  dsimp only
  let ell := actualCavityDepth a d N z-1
  let r := effectiveModelRadius a d N β
  let T := graphBallVertices g.graph o ell
  let Rstruct := logarithmicRadius (c/4) d N
  let gnew := g.labelledResampledGraph T labels samples (Rstruct/4)
  let L := Real.log (N:ℝ)
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  intro htarget K Rmodel hbudget hdiam hdiamlog hcapture x y
  let M := gnew.filledExteriorModel T K
  let e : T → filledExteriorVertices T K := fun x => ⟨x.val,Or.inl x.property⟩
  have num := hnum z hz hfloor
  have hL : 1≤L := num.log_one
  have hLp : 0<L := by linarith
  have hε : 0≤ε := num.error_nonnegative
  have hεScaled : ε*L^4≤1 := by
    have hC1sq : 1≤C1^2 := one_le_pow₀ hC1
    exact (mul_le_mul_of_nonneg_right (le_mul_of_one_le_left hε hC1sq) (pow_nonneg hLp.le 4)).trans num.error_scaled
  have hεOne : ε≤1 :=
    (le_mul_of_one_le_right hε (one_le_pow₀ hL)).trans hεScaled
  have hrlog : ((4*r+1:ℕ)+1:ℝ)≤A*L :=
    num.pair_log.trans (mul_le_mul_of_nonneg_right hA hLp.le)
  have hloc := M.componentwise_pair_localization_feedback hd hbudget (gnew.Q z) z hz
    (gnew.Q_im_nonnegative z hz) B hzB ε L A hε hεOne hL hA0 hεScaled htarget.2.1
    Rmodel r hdiam hdiamlog hrlog hlarge (e x) (e y)
  have hid := gnew.deficient.restrict_pair_P (filledExteriorVertices T K) (e x) (e y) r
    (hcapture x) (hcapture y) (gnew.Q z) z
  have hid' : M.P r z (gnew.Q z) (e x) (e y)=gnew.P r z (gnew.Q z) x.val y.val :=
    hid.trans (gnew.deficient_P r z (gnew.Q z) x.val y.val)
  rw [hid'] at hloc
  have hfixed' := hfixed g o z hz hzB hfloor Cq badCount hplus labels samples htarget x y
  have htail := effectiveModelRadius_localization_tail a d N β hd hL hmargin.1 z hz.le
  have htailAbs : DeficientGraph.localizationTailConstant d*physicalTransfer d z^(2*r)≤ε/L^2 := by
    calc
      _ ≤ DeficientGraph.localizationTailConstant d*(κ*ε/L^(4*a)) := mul_le_mul_of_nonneg_left htail hTail
      _ = Ktail*ε/L^(4*a) := by dsimp only [Ktail]; ring
      _ ≤ _ := constant_div_log_absorption (4*a) 2 L ε Ktail hL hε htailLarge (by omega)
  have hlocal : ‖gnew.P r z (gnew.Q z) x.val y.val-gnew.filledRetainedGreen T K (gnew.Q z) z x y‖≤
      DeficientGraph.localizationFeedbackConstant d B A*L*gnew.sourceFeedback z+ε/L^2 := by
    have hh := hloc.trans (add_le_add_left htailAbs _)
    have hentry : M.extensionGreen (gnew.Q z) z (e x) (e y)=gnew.filledRetainedGreen T K (gnew.Q z) z x y := rfl
    rw [hentry] at hh
    simpa only [sourceFeedback,norm_sub_rev] using hh
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (g.sourceRetainedReference T r (g.Q z) z x y) (gnew.P r z (gnew.Q z) x.val y.val)
    (gnew.filledRetainedGreen T K (gnew.Q z) z x y)
  exact (ht.trans (add_le_add hfixed' hlocal)).trans_eq (by ring)

end RegularGraph
end LocalLaw
