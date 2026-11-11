import SpectralConsequences.OldBallInverseRows
import LocalLaw.EffectiveAugmentedMargins

/-! # Constant physical retained-ball inverse rows on the original weak event -/

open Filter
open scoped BigOperators
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance sourceOldBallInverseDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem eventually_source_old_ball_inverse_rows (a b d : ℕ) (c β B : ℝ)
    (ha : 12 ≤ a) (hb : 25*a ≤ b) (hd : 3 ≤ d) (hc : 0 < c)
    (hβ : 0 < β) (hβc : β ≤ c/32) (hB : 0 ≤ B) :
    ∀ᶠ N : ℕ in atTop, ∀ (g : RegularGraph N d) (o : Fin N) (z : ℂ),
      0 < z.im → Real.log (N : ℝ)^b/(N : ℝ) ≤ z.im → ‖z‖ ≤ B → ∀ badCount : ℕ,
      g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (finiteOmega d) badCount z →
      let T := graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let U := (g.G z).submatrix (Subtype.val : T → Fin N) (Subtype.val : T → Fin N)
      (∀ i, ∑ j, ‖U⁻¹ i j‖ ≤ 2*DeficientGraph.boundarySchurConstant d B) ∧
        (∀ j, ∑ i, ‖U⁻¹ i j‖ ≤ 2*DeficientGraph.boundarySchurConstant d B) := by
  have hdepth := (lowerLogLogRadius_tendsto a d (by omega) hd).eventually (eventually_ge_atTop 4)
  filter_upwards [eventually_sourceDeletionBounds a b d β B ha hb hd hβ hB,
    RegularGraph.eventually_actual_inner_complement_nonempty a d (by omega) hd,
    eventually_effective_augmented_radius_margin a d c β hd hc hβ hβc,
    eventually_resampling_radius_margin a d 2 8 β hd hβ,
    eventually_log_ge_nat (((d-1 : ℕ) : ℝ)),hdepth]
    with N hnum hnonempty hmargin hroom hlog hdepthN
  intro g o z hz hfloor hzB badCount hsource
  dsimp only
  let ell := actualCavityDepth a d N z-1
  let r := effectiveModelRadius a d N β
  let R := logarithmicRadius (c/4) d N
  have hell : ell ≤ doubleLogRadius a d N := (actualCavityDepth_radius_bounds a d N z hdepthN).2
  have hrad := hmargin ell hell
  have hr : 1 ≤ r := by dsimp only [r,effectiveModelRadius,modelRadiusLoss]; omega
  have hgeom : 6*(ell+r)+2 ≤ R := by dsimp only [R] at *; omega
  have hroom' : modelRadiusLoss a d N ≤ logarithmicRadius β d N := by
    dsimp only [modelRadiusLoss]
    omega
  let w := Classical.choice (hnonempty g o z)
  exact old_ball_inverse_rows g (hnum z hz hfloor) (by omega) hd hβ.le hlog hroom' R hr hgeom
    hsource.1.1 (g.Q z) hz (g.Q_im_nonnegative z hz) hzB hsource.2.1 hsource.2.2 o w

end SpectralConsequences
