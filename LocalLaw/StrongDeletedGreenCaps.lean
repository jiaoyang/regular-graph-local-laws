import LocalLaw.DeletedPairBudget
import LocalLaw.SourceObservationParameters
import LocalLaw.IndependentRadiusEvents
import LocalLaw.EffectiveAugmentedMargins

/-! Global deleted entry caps from an actual retained strong structural event. -/
noncomputable section
namespace LocalLaw
local instance strongDeletedGreenCapsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph

theorem eventually_strong_deleted_green_caps (a b d : ℕ) (c β B C1 : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c)
    (hβ : 0<β) (hβc : β≤c/32) (hC1 : 1≤C1) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0<z.im → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → ∀ Cq badCount : ℕ,
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1)
        (finiteOmega d) Cq badCount C1 o z →
      (∀ v,graphBallExcess g.graph v (logarithmicRadius (c/4) d N)≤finiteOmega d) →
      let T := graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      ∀ x y : (Tᶜ : Set (Fin N)), ‖(g.deficient.delete T).G z x y‖≤2*finiteExtraReferenceConstant d+1 := by
  have hCextra := finiteExtraReferenceConstant_ge_one d hd
  filter_upwards [eventually_sourceObservationBounds a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_effective_augmented_radius_margin a d c β hd hc hβ hβc,
    (lowerLogLogRadius_tendsto a d (by omega) hd).eventually (Filter.eventually_ge_atTop 4)]
    with N hnum hmargin hdepth
  intro g o z hz hfloor Cq badCount hplus hstrong
  dsimp only
  let ell := actualCavityDepth a d N z-1
  let r := effectiveModelRadius a d N β
  let R := logarithmicRadius (c/4) d N
  let T := graphBallVertices g.graph o ell
  let old := g.deficient.delete T
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  let L := Real.log (N:ℝ)
  have hell : ell≤doubleLogRadius a d N := (actualCavityDepth_radius_bounds a d N z hdepth).2
  have hm : 4*r+2*ell+2≤R := by have hh:=hmargin ell hell; omega
  have num := hnum z hz hfloor
  have hε : 0≤ε := num.error_nonnegative
  have hL : 0≤L := (by norm_num : (0:ℝ)≤1).trans num.log_one
  have hprior := hplus.cavity.trans (scalarScale_constant_absorption (spectralScale z) ε C1
    (spectralScale_pos hz) hε hC1)
  have hfeedback := (DeficientGraph.weak_localization_feedback_budgets d hd z (g.Q z) hz B
    (C1^2*ε) L (sourceObservationLogCap d β) (mul_nonneg (sq_nonneg C1) hε) num.log_one
      num.log_cap_nonnegative num.error_scaled hprior (4*r+1) (4*r+1) num.pair_log num.pair_log num.localization_large).1
  have herror : C1*L^3*ε≤1 := by
    have hC1sq : C1≤C1^2 := by nlinarith
    have hpow : L^3≤L^4 := pow_le_pow_right₀ num.log_one (by omega)
    calc
      _ ≤ C1^2*L^4*ε := mul_le_mul_of_nonneg_right
        (mul_le_mul hC1sq hpow (pow_nonneg hL _) (sq_nonneg C1)) hε
      _ = (C1^2*ε)*L^4 := by ring
      _ ≤ 1 := num.error_scaled
  have htone : physicalTransfer d z≤1 := by nlinarith [physicalTransfer_sq_le_half d hd z,physicalTransfer_pos d hd z]
  intro x y
  let S := pairBallVertices old.graph x y r
  let M := old.restrict S
  have hbudget := g.deleted_pair_component_finiteReferenceBudget o ell r R hm hstrong x y
  have hkernel := M.componentwise_finite_kernel_decay hd hbudget (g.Q z) z hz (g.Q_im_nonnegative z hz)
    (4*r+1) (pairBall_distance_bound old.graph x y r) hfeedback (pairBallLeft old.graph x y r) (pairBallRight old.graph x y r)
  have hcap : ‖g.deletedP T r z (g.Q z) x y‖≤2*finiteExtraReferenceConstant d :=
    hkernel.trans (mul_le_of_le_one_right (by positivity) (pow_le_one₀ (physicalTransfer_pos d hd z).le htone))
  have hh := norm_sub_le_norm_sub_add_norm_sub (old.G z x y) (g.deletedP T r z (g.Q z) x y) 0
  simp only [sub_zero] at hh
  have happ : ‖old.G z x y-g.deletedP T r z (g.Q z) x y‖≤C1*L^3*ε := by
    simpa only [sourcePrime,inflatedPrime,mul_assoc] using hplus.deleted x y
  exact (hh.trans (add_le_add happ hcap)).trans (by linarith)

end RegularGraph
end LocalLaw
