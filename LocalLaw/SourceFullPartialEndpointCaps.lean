import LocalLaw.SourceFullPartialInputs
import LocalLaw.ActualFullEndpointRowCaps
import LocalLaw.FullVacuumLogParameters
import LocalLaw.SourceFormalEdgeBounds

/-! # Actual full partial-endpoint caps with every source budget realized -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance sourceFullPartialEndpointCapsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 3000000

def sourceFullEndpointRowConstant (d : ℕ) (β : ℝ) : ℝ :=
  5+((d:ℝ)+2)*sourceFullCutRowConstant d β

namespace RegularGraph

theorem eventually_source_full_partial_endpoint_caps (a b d : ℕ) (c β B C1 : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c)
    (hβ : 0<β) (hβc : β≤c/32) (hC1 : 1≤C1) :
    ∀ᶠ N : ℕ in Filter.atTop,∀ (g : RegularGraph N d) (o : Fin N) (z q : ℂ),
      0<z.im → ‖z‖≤B → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → 0≤q.im →
      ‖q-semicircleRoot z‖≤C1*scalarScale (spectralScale z)
        (graphPaperError a d N (logarithmicRadius β d N) z) →
      (∀v,graphBallExcess g.graph v (logarithmicRadius (c/4) d N)≤finiteOmega d) →
      ∀{ι : Type}[Fintype ι]
      (labels : ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (x y : Fin N),
      let T := graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let selector := logarithmicRadius (c/4) d N/4
      let r := effectiveModelRadius a d N β
      let s := g.admissibleState T labels samples
      ∀(hs : 1≤selector)(S : Set (Fin N)),S⊆s.fullTwoTargetVertices selector r x y →
      let e := s.fullPartialEmbedding selector S hs
      let H := ((g.labelledResampledGraph T labels samples selector).deficient.restrict S).extensionGreen q z
      (∀i,∑j,‖H (e i) (e j)‖≤sourceFullEndpointRowConstant d β*Real.log (N:ℝ)^(a-1)) ∧
      (∀j,∑i,‖H (e i) (e j)‖≤sourceFullEndpointRowConstant d β*Real.log (N:ℝ)^(a-1)) := by
  let A := fullRestrictionLogCap d β
  let U := fullEndpointCountConstant d
  let M := sourceFullCutRowConstant d β
  let D := sourceFullCovarianceConstant d β B C1
  let V := 4+((d:ℝ)+2)*M
  let w := 4*(d:ℝ)/Real.sqrt ((d:ℝ)-1)
  let Hbudget := max 1 (max (2*U*(1+V*w)*w*D) (2*U*(1+V*w)^2*D))
  have hA := (fullRestrictionLogCap_properties d β).1
  have hU : 0≤U := by dsimp only [U,fullEndpointCountConstant]; positivity
  have hExtra : 0≤finiteExtraReferenceConstant d := (by norm_num : (0:ℝ)≤1).trans (finiteExtraReferenceConstant_ge_one d hd)
  have hM : 0≤M := by dsimp only [M,sourceFullCutRowConstant]; exact add_nonneg (mul_nonneg hU (by positivity)) (by norm_num)
  have hD : 0≤D := by dsimp only [D,sourceFullCovarianceConstant]; positivity
  have hV : 0≤V := by dsimp only [V]; positivity
  have hw : 0≤w := by dsimp only [w]; positivity
  have hH : 1≤Hbudget := le_max_left _ _
  have hAobs := (fullRestrictionLogCap_properties d β).2.1
  filter_upwards [eventually_source_full_partial_inputs a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_sourceObservationBounds_of_cap a b d c β B C1 A ha hb hd hc hβ hβc hC1 hAobs,
    eventually_source_formal_kernel_bounds a b d c β B C1 A ha hb hd hc hβ hβc hC1 hA,
    eventually_source_formal_edge_bounds a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_actual_fullPartialIndex_count a d ha hd,
    eventually_paperError_sharp_log_small a b d β Hbudget ha hb hd hβ hH]
    with N hinputs hnum hformal hedge hcount hsharp
  intro g o z q hz hzB hfloor hq hprior hballs ι _ labels samples x y
  dsimp only
  let T := graphBallVertices g.graph o (actualCavityDepth a d N z-1)
  let selector := logarithmicRadius (c/4) d N/4
  let r := effectiveModelRadius a d N β
  let s := g.admissibleState T labels samples
  let p := rationalTreeReference (d-1) q
  let L := Real.log (N:ℝ)
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  have num := hnum z hz hfloor
  have hf := hformal z q hz hzB hfloor hprior
  have he := hedge z q hz hzB hfloor hprior
  have hL0 : 0≤L := by linarith [num.log_one]
  have hpow : 1≤L^(a-1) := one_le_pow₀ num.log_one
  intro hs S hSS
  let C := M*L^(a-1)
  let δ := D*L*ε
  let Cbench := 4+((d:ℝ)+2)*C
  let n : ℝ := Fintype.card (s.FullEndpointIndex selector S)
  have hin := hinputs g o z q hz hzB hfloor hq hprior hballs labels samples x y hs S hSS
  have hcountN : n≤U*L^(2*a-4) := by
    simpa only [Nat.card_eq_fintype_card] using hcount g o z labels samples selector hs S
  have hC : 0≤C := mul_nonneg hM (pow_nonneg hL0 _)
  have hδ : 0≤δ := mul_nonneg (mul_nonneg hD hL0) num.error_nonnegative
  have hCbench : 0≤Cbench := by dsimp only [Cbench]; positivity
  have hRow : Cbench≤V*L^(a-1) := by dsimp only [Cbench,C,V]; nlinarith only [hpow]
  have hbud := full_vacuum_log_budgets a L ε n Cbench U V w D Hbudget (by omega) num.log_one
    num.error_nonnegative (Nat.cast_nonneg _) hCbench hU hV hw hD hH hcountN hRow
    ((le_max_left _ _).trans (le_max_right _ _)) ((le_max_right _ _).trans (le_max_right _ _))
    (hsharp z hz hfloor)
  have hcaps := g.full_partial_model_vacuum_row_caps hd T labels samples selector hs S q p z hz hq
    hf.1 hf.2.1 hf.2.2.2.1 4 C δ (by norm_num) hC hδ (he.1.trans (by norm_num)) hf.2.2.1 he.2
    hin.2 hin.1 hbud.1 hbud.2
  have hfinal : 4+((d:ℝ)+2)*C+1≤sourceFullEndpointRowConstant d β*L^(a-1) := by
    dsimp only [sourceFullEndpointRowConstant,C]
    nlinarith only [hpow]
  exact ⟨fun i=>(hcaps.1 i).trans hfinal,fun j=>(hcaps.2 j).trans hfinal⟩

end RegularGraph
end LocalLaw
