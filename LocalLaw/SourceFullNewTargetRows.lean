import LocalLaw.SourceFullPartialTargetRows
import LocalLaw.SourceFullPartialEndpointCaps
import LocalLaw.FullTargetRowTransfer

/-! # New full-model target rows with all source hypotheses realized -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance sourceFullNewTargetRowsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def fullModelCouplingCap (d : ℕ) : ℝ := 4*(d:ℝ)/Real.sqrt ((d:ℝ)-1)

def sourceFullTargetRowConstant (d : ℕ) (β : ℝ) : ℝ :=
  sourceFullCutRowConstant d β*(1+fullModelCouplingCap d*sourceFullEndpointRowConstant d β)

theorem sourceFullCutRowConstant_nonnegative (d : ℕ) (β : ℝ) : 0≤sourceFullCutRowConstant d β := by
  have hA := (fullRestrictionLogCap_properties d β).1
  have hU : 0≤fullEndpointCountConstant d := by unfold fullEndpointCountConstant; positivity
  unfold sourceFullCutRowConstant
  positivity

theorem sourceFullEndpointRowConstant_nonnegative (d : ℕ) (β : ℝ) : 0≤sourceFullEndpointRowConstant d β := by
  have hM := sourceFullCutRowConstant_nonnegative d β
  unfold sourceFullEndpointRowConstant
  positivity

theorem sourceFullTargetRowConstant_nonnegative (d : ℕ) (β : ℝ) : 0≤sourceFullTargetRowConstant d β := by
  have hM := sourceFullCutRowConstant_nonnegative d β
  have hN := sourceFullEndpointRowConstant_nonnegative d β
  unfold sourceFullTargetRowConstant fullModelCouplingCap
  positivity

namespace RegularGraph

theorem eventually_source_full_new_target_rows (a b d : ℕ) (c β B C1 : ℝ)
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
      ∀v:S,(∑j,‖H v (e j)‖)≤sourceFullTargetRowConstant d β*Real.log (N:ℝ)^(2*a-2) := by
  filter_upwards [eventually_source_full_partial_target_rows a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_source_full_partial_endpoint_caps a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_source_formal_edge_bounds a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_log_ge_nat 1] with N hOld hNew hedge hL
  intro g o z q hz hzB hfloor hq hprior hballs ι _ labels samples x y
  dsimp only
  let T := graphBallVertices g.graph o (actualCavityDepth a d N z-1)
  let selector := logarithmicRadius (c/4) d N/4
  let L := Real.log (N:ℝ)
  let M := sourceFullCutRowConstant d β
  let V := sourceFullEndpointRowConstant d β
  have hM := sourceFullCutRowConstant_nonnegative d β
  have hV := sourceFullEndpointRowConstant_nonnegative d β
  have hPa : 1≤L^(a-1) := one_le_pow₀ hL
  have he := hedge z q hz hzB hfloor hprior
  intro hs S hSS v
  have ho := hOld g o z q hz hzB hfloor hq hprior hballs labels samples x y hs S hSS v
  have hn := hNew g o z q hz hzB hfloor hq hprior hballs labels samples x y hs S hSS
  have hh := g.full_new_target_endpoint_row hd T labels samples selector hs S q z hz hq
    (by simpa only [mul_comm] using he.2) (M*L^(a-1)) (V*L^(a-1))
    (by positivity) (by positivity) v ho hn.1
  have hp : (L^(a-1))^2=L^(2*a-2) := by rw [←pow_mul]; congr 1; omega
  have hm : M*L^(a-1)≤M*(L^(a-1))^2 := mul_le_mul_of_nonneg_left (by nlinarith only [hPa]) hM
  refine hh.trans ?_
  dsimp only [sourceFullTargetRowConstant,fullModelCouplingCap]
  calc
    _ = M*L^(a-1)+(M*(4*(d:ℝ)/Real.sqrt ((d:ℝ)-1))*V)*(L^(a-1))^2 := by ring
    _ ≤ M*(L^(a-1))^2+(M*(4*(d:ℝ)/Real.sqrt ((d:ℝ)-1))*V)*(L^(a-1))^2 := add_le_add_right hm _
    _ = _ := by rw [hp]; ring

end RegularGraph
end LocalLaw
