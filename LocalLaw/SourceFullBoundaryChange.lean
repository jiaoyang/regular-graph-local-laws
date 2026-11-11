import LocalLaw.SourceFullBoundaryContinuity
import LocalLaw.SharpParameterSmallness

/-! # Literal full pair-model boundary change at the first-stage tolerance

Only the full tolerance 1/log N is needed. The polynomial-log continuity
cost is absorbed by the actual sharp nominal error and Q-change budget.
-/

noncomputable section
namespace LocalLaw
local instance sourceFullBoundaryChangeDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph

theorem eventually_source_full_boundary_change (a b d : ℕ) (c β B C1 : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c)
    (hβ : 0<β) (hβc : β≤c/32) (hC1 : 1≤C1) :
    ∀ᶠ N : ℕ in Filter.atTop,∀ (g : RegularGraph N d) (o : Fin N) (z q v : ℂ),
      0<z.im → ‖z‖≤B → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → 0≤q.im → 0≤v.im →
      ‖q-semicircleRoot z‖≤C1*scalarScale (spectralScale z) (graphPaperError a d N (logarithmicRadius β d N) z) →
      ‖v-semicircleRoot z‖≤C1*scalarScale (spectralScale z) (graphPaperError a d N (logarithmicRadius β d N) z) →
      ‖q-v‖≤graphPaperError a d N (logarithmicRadius β d N) z/Real.log (N:ℝ)^16 →
      (∀w,graphBallExcess g.graph w (logarithmicRadius (c/4) d N)≤finiteOmega d) →
      ∀{ι : Type}[Fintype ι]
      (labels : ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let T := graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let h := g.labelledResampledGraph T labels samples (logarithmicRadius (c/4) d N/4)
      let r := effectiveModelRadius a d N β
      ∀x y,‖h.P r z q x y-h.P r z v x y‖≤1/Real.log (N:ℝ) := by
  let K := sourceFullContinuityConstant d β
  let H := max 1 K
  have hK : 0≤K := sourceFullContinuityConstant_nonnegative d β
  have hH : 1≤H := le_max_left _ _
  have hKH : K≤H := le_max_right _ _
  filter_upwards [eventually_source_full_boundary_continuity a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_paperError_sharp_log_small a b d β H ha hb hd hβ hH,
    eventually_effectiveModelRadius_common_ball_margin a d c β hd hc hβ hβc,
    eventually_log_ge_nat 1,Filter.eventually_ge_atTop 1] with N hcontinuity hsharp hcommon hL hN
  intro g o z q v hz hzB hfloor hq hv hpriorQ hpriorV hchange hballs ι _ labels samples
  dsimp only
  let T := graphBallVertices g.graph o (actualCavityDepth a d N z-1)
  let R := logarithmicRadius (c/4) d N
  let selector := R/4
  let r := effectiveModelRadius a d N β
  let s := g.admissibleState T labels samples
  let h := g.labelledResampledGraph T labels samples selector
  let L := Real.log (N:ℝ)
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  have hLp : 0<L := by linarith
  have hε : 0≤ε := graphPaperError_nonnegative a d N _ z hN hz.le
  have hp0 : 0≤ε*L^(4*a+1) := by positivity
  have hHscaled : H*(ε*L^(4*a+1))≤1 := by
    have hh := mul_le_mul_of_nonneg_left (hsharp z hz hfloor) (show 0≤H by linarith)
    simpa only [mul_inv_cancel₀ (show H≠0 by linarith)] using hh
  have hKscaled : K*(ε*L^(4*a+1))≤1 :=
    (mul_le_mul_of_nonneg_right hKH hp0).trans hHscaled
  have hs : 1≤selector := by
    dsimp only [selector,R]
    omega
  intro x y
  let S := pairBallVertices (s.fullResample selector).graph x y r
  let M := h.deficient.restrict S
  let xl := pairBallLeft (s.fullResample selector).graph x y r
  let yl := pairBallRight (s.fullResample selector).graph x y r
  have hS : S⊆s.fullTwoTargetVertices selector r x y := s.switched_full_pair_subset_old_augmentation selector r x y
  have hh := hcontinuity g o z q v hz hzB hfloor hq hv hpriorQ hpriorV hballs labels samples x y hs S hS xl yl
  rw [←h.deficient_P r z q x y,←h.deficient_P r z v x y]
  change ‖M.extensionGreen q z xl yl-M.extensionGreen v z xl yl‖≤1/L
  apply hh.trans
  change K*L^(4*a+1)*‖q-v‖≤1/L
  calc
    _ ≤ K*L^(4*a+1)*(ε/L^16) := mul_le_mul_of_nonneg_left hchange (by positivity)
    _ = (K*(ε*L^(4*a+1)))/L^16 := by ring
    _ ≤ 1/L^16 := div_le_div_of_nonneg_right hKscaled (pow_nonneg hLp.le _)
    _ ≤ 1/L := one_div_le_one_div_of_le hLp (by
      simpa only [pow_one] using pow_le_pow_right₀ hL (show 1≤16 by norm_num))

end RegularGraph
end LocalLaw
