import LocalLaw.CavityMinorModelBounds
import LocalLaw.BoundaryMaxPowerParameters
import LocalLaw.SourceObservationParameters

/-! # Actual source cavity-minor profiles and deterministic weight budgets -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance sourceCavityMinorProfileDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph

theorem eventually_source_cavity_minor_profile (a b d : ℕ) (c β B C1 : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c)
    (hβ : 0<β) (hβc : β≤c/32) (hC1 : 1≤C1) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0<z.im → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → ∀ Cq badCount : ℕ,
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1) (finiteOmega d) Cq badCount C1 o z →
      let ell := actualCavityDepth a d N z-1
      let T := graphBallVertices g.graph o ell
      let L := Real.log (N:ℝ)
      let A := sourceObservationLogCap d β
      ∃ hell : 2≤ell, ∀ (j : T) (hjo : g.graph.Adj j.val o), (graphBall g.graph o ell).IsTree →
        let P := ((g.deficient.restrict T).deleteVertex j).extensionGreen (g.Q z) z
        let root := g.truncatedCavityRoot o ell j hjo
        let l := g.truncatedCavityBoundaryInner o ell hell j hjo
        let w := g.truncatedCavityWeight o ell hell j hjo (g.Q z) z
        Nonempty (BoundaryMaxProfile P l root a L ((d:ℝ)*((d:ℝ)+1))
          (2*finiteExtraReferenceConstant d*((d:ℝ)+1)) (8*(d:ℝ)*finiteExtraReferenceConstant d^2*A)) ∧
          (∑ α,‖w α‖)≤(8*(d:ℝ)*finiteExtraReferenceConstant d^2*A)*L ∧
          Real.sqrt (∑ α,‖w α‖^2)≤(32*(d:ℝ)*finiteExtraReferenceConstant d^4*A+1)*L/resamplingDecayDenominator d ell ∧
          ∀ α,‖w α‖≤4*finiteExtraReferenceConstant d^2/resamplingDecayDenominator d ell := by
  have hdepth := (lowerLogLogRadius_tendsto a d (by omega) hd).eventually (Filter.eventually_ge_atTop 4)
  filter_upwards [eventually_sourceObservationBounds a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_resampling_radius_margin a d 3 6 β hd hβ,hdepth] with N hnum hroom hdepth
  intro g o z hz hfloor Cq badCount hplus
  dsimp only
  let ell := actualCavityDepth a d N z-1
  let T := graphBallVertices g.graph o ell
  let r := effectiveModelRadius a d N β
  let L := Real.log (N:ℝ)
  let A := sourceObservationLogCap d β
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  let Robs := singletonObservationDiameter d r
  let Rminor := (finiteOmega d+1)*(4*ell+1)
  let C := finiteExtraReferenceConstant d
  let n := (Nat.card (BoundaryOrientedEdge g.graph T):ℝ)
  let M := 2*C*physicalTransfer d z^ell
  let W := 8*(d:ℝ)*C^2*((Rminor:ℝ)+1)
  have hdepthBounds := actualCavityDepth_radius_bounds a d N z hdepth
  have hell : 2≤ell := by
    have hh : (2:ℝ)≤(ell:ℝ) := by have hp := hdepthBounds.1; dsimp only [ell]; linarith
    exact_mod_cast hh
  have hellr : ell≤r := by
    change ell≤logarithmicRadius β d N-(2*doubleLogRadius a d N+4)
    have hh := hdepthBounds.2
    change ell≤doubleLogRadius a d N at hh
    omega
  have hR : Rminor≤Robs := by
    dsimp only [Rminor,Robs,singletonObservationDiameter]
    exact Nat.mul_le_mul_left _ (by omega)
  have num := hnum z hz hfloor
  have hprior := hplus.cavity.trans (scalarScale_constant_absorption (spectralScale z) ε C1
    (spectralScale_pos hz) num.error_nonnegative hC1)
  have hfeedback := (DeficientGraph.weak_localization_feedback_budgets d hd z (g.Q z) hz B (C1^2*ε) L A
    (mul_nonneg (sq_nonneg C1) num.error_nonnegative) num.log_one num.log_cap_nonnegative num.error_scaled
    hprior Robs (4*r+1) num.diameter_log num.pair_log num.localization_large).1
  have hminorFeedback : ‖g.Q z-semicircleRoot z‖*C*coreConvolutionConstant (finiteOmega d+1)*((Rminor:ℝ)+1)≤1/2 := by
    have hcoef : 0≤‖g.Q z-semicircleRoot z‖*C*coreConvolutionConstant (finiteOmega d+1) := by
      have hh := coreConvolutionConstant_nonnegative (finiteOmega d+1)
      have hC := (finiteExtraReferenceConstant_ge_one d hd)
      dsimp only [C]
      positivity
    exact (mul_le_mul_of_nonneg_left (add_le_add_right (Nat.cast_le.mpr hR) 1) hcoef).trans hfeedback
  have hRlog : (Rminor:ℝ)+1≤A*L :=
    (add_le_add_right (Nat.cast_le.mpr hR) 1).trans num.diameter_log
  refine ⟨hell,?_⟩
  intro j hjo hTree
  have hp := g.truncatedMinor_max_budgets hd o ell hell j hjo hTree (g.Q z) z hz
    (g.Q_im_nonnegative z hz) hminorFeedback
  have hw := g.truncatedCavityWeight_log_bounds hd o ell hell j hjo hTree (g.Q z) z hz
    (g.Q_im_nonnegative z hz) hminorFeedback A L num.log_cap_nonnegative num.log_one hRlog
  have hC : 0≤C := (by norm_num : (0:ℝ)≤1).trans (finiteExtraReferenceConstant_ge_one d hd)
  have ht : 0≤physicalTransfer d z := (physicalTransfer_pos d hd z).le
  have hM : 0≤M := by dsimp only [M]; positivity
  have hW : 0≤W := by dsimp only [W]; positivity
  refine ⟨⟨⟨M,Real.sqrt (n*W),W,hM,Real.sqrt_nonneg _,hW,hp.1,hp.2.1,?_,?_,?_,?_⟩⟩,hw⟩
  · simpa only [n,Nat.card_eq_fintype_card] using hp.2.2.1.le
  · simpa only [Nat.card_eq_fintype_card] using hp.2.2.2
  · simpa only [Nat.card_eq_fintype_card] using g.boundary_card_log_bound o a ell hd num.log_one hdepthBounds.2
  · have hh := mul_le_mul_of_nonneg_left hRlog (show 0≤8*(d:ℝ)*C^2 by positivity)
    exact hh.trans_eq (by dsimp only [W,A,C,L]; ring)

end RegularGraph
end LocalLaw
