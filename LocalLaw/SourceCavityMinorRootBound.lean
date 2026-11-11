import LocalLaw.SourceCavityMinorProfile

/-! # The actual cavity reference root has nine inverse logarithms of decay -/

noncomputable section
namespace LocalLaw
local instance sourceCavityMinorRootBoundDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph

theorem eventually_source_cavity_minor_root_bound (a b d : ℕ) (c β B C1 : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c)
    (hβ : 0<β) (hβc : β≤c/32) (hC1 : 1≤C1) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0<z.im → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → ∀ Cq badCount : ℕ,
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1) (finiteOmega d) Cq badCount C1 o z →
      let ell := actualCavityDepth a d N z-1
      let T := graphBallVertices g.graph o ell
      ∃ hell : 2≤ell, ∀ (j : T) (hjo : g.graph.Adj j.val o), (graphBall g.graph o ell).IsTree →
      ∀ α, ‖((g.deficient.restrict T).deleteVertex j).extensionGreen (g.Q z) z
          (g.truncatedCavityRoot o ell j hjo) (g.truncatedCavityBoundaryInner o ell hell j hjo α)‖≤
        2*finiteExtraReferenceConstant d/Real.log (N:ℝ)^9 := by
  have hdepth := (lowerLogLogRadius_tendsto a d (by omega) hd).eventually (Filter.eventually_ge_atTop 4)
  filter_upwards [eventually_sourceObservationBounds a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_resampling_radius_margin a d 3 6 β hd hβ,hdepth] with N hnum hroom hdepth
  intro g o z hz hfloor Cq badCount hplus
  dsimp only
  let ell := actualCavityDepth a d N z-1
  let r := effectiveModelRadius a d N β
  let L := Real.log (N:ℝ)
  let A := sourceObservationLogCap d β
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  let Robs := singletonObservationDiameter d r
  let Rminor := (finiteOmega d+1)*(4*ell+1)
  let C := finiteExtraReferenceConstant d
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
      have hC := finiteExtraReferenceConstant_ge_one d hd
      dsimp only [C]
      positivity
    exact (mul_le_mul_of_nonneg_left (add_le_add_right (Nat.cast_le.mpr hR) 1) hcoef).trans hfeedback
  refine ⟨hell,?_⟩
  intro j hjo hTree α
  have hh := g.truncatedMinor_root_boundary_bound hd o ell hell j hjo hTree (g.Q z) z hz
    (g.Q_im_nonnegative z hz) hminorFeedback α
  have hL : 0<L := by have hp := num.log_one; dsimp only [L]; linarith
  have hgain := selected_radius_decay_gain a d N z ha hd num.log_one
  have htail : physicalTransfer d z^ell≤(L^9)⁻¹ :=
    (physicalTransfer_resampling_gain d ell hd z).trans
      ((inv_le_inv₀ (resamplingDecayDenominator_pos d ell hd) (pow_pos hL 9)).mpr hgain)
  have hC : 0≤2*finiteExtraReferenceConstant d := by linarith [finiteExtraReferenceConstant_ge_one d hd]
  exact hh.trans ((mul_le_mul_of_nonneg_left htail hC).trans_eq (by ring))

end RegularGraph
end LocalLaw
