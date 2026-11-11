import LocalLaw.PartialTargetRowTransfer
import LocalLaw.SupportedBoundaryContinuity

/-! # Boundary continuity of the actual switched partial model

Only the OLD model has a finite reference budget. The supported inverse
identity, actual crossing charges and new endpoint rows supply square-row
estimates for the switched model at both boundary parameters.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance actualPartialBoundaryContinuityDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace RegularGraph
variable {N d:ℕ} {ι:Type} [Fintype ι]

theorem partial_model_boundary_continuity (g:RegularGraph N d) (hd:3≤d)
    (T:Set (Fin N)) (labels:ι≃BoundaryOrientedEdge g.graph T) (samples:LocalSamplingFiber g.graph T)
    (selector:ℕ) (S:Set (Tᶜ:Set (Fin N)))
    (hbudget:((g.deficient.delete T).restrict S).ComponentFiniteReferenceBudget)
    (q v z:ℂ) (hz:0<z.im) (hq:0≤q.im) (hv:0≤v.im) (hqnorm:‖q‖≤2) (hvnorm:‖v‖≤2)
    (R:ℕ) (hR:∀x y,((g.deficient.delete T).restrict S).graph.dist x y≤R)
    (smallQ:‖q-semicircleRoot z‖*finiteExtraReferenceConstant d*coreConvolutionConstant (finiteOmega d+1)*
      ((R:ℝ)+1)≤1/2)
    (smallV:‖v-semicircleRoot z‖*finiteExtraReferenceConstant d*coreConvolutionConstant (finiteOmega d+1)*
      ((R:ℝ)+1)≤1/2)
    (a b Cq Cv:ℝ) (ha:0≤a) (hb:0≤b) (hCq:0≤Cq) (hCv:0≤Cv) :
    let s:=g.admissibleState T labels samples
    let e:=s.partialEndpointEmbedding selector S
    let Gq:=((g.deficient.delete T).restrict S).extensionGreen q z
    let Gv:=((g.deficient.delete T).restrict S).extensionGreen v z
    let M:=((g.labelledResampledGraph T labels samples selector).deficient.delete T).restrict S
    ∀x y:S,(∑i,‖Gq x (e i)‖)≤a→(∑i,‖Gv y (e i)‖)≤b→
      (∀i,∑j,‖M.extensionGreen q z (e i) (e j)‖≤Cq)→
      (∀i,∑j,‖M.extensionGreen v z (e i) (e j)‖≤Cv)→
      ‖M.extensionGreen q z x y-M.extensionGreen v z x y‖≤
        32*finiteExtraReferenceConstant d^2*
          (2+(a*(1+4*Cq)*4)^2+(b*(1+4*Cv)*4)^2)*((R:ℝ)+1)*‖q-v‖ := by
  dsimp only
  let s:=g.admissibleState T labels samples
  let e:=s.partialEndpointEmbedding selector S
  let old:=(g.deficient.delete T).restrict S
  let new:=((g.labelledResampledGraph T labels samples selector).deficient.delete T).restrict S
  intro x y hOldQ hOldV hNewQ hNewV
  have hrowQ:=g.partial_new_target_endpoint_row hd T labels samples selector S q z hz hq hqnorm
    a Cq ha hCq x hOldQ hNewQ
  have hrowV:=g.partial_new_target_endpoint_row hd T labels samples selector S v z hz hv hvnorm
    b Cv hb hCv y hOldV hNewV
  exact old.supported_two_parameter_continuity new hd hbudget e q v z hz hq hv R hR smallQ smallV
    (g.partial_model_difference_supported T labels samples selector S q z)
    (g.partial_model_difference_supported T labels samples selector S v z)
    (a*(1+4*Cq)) (b*(1+4*Cv)) 4 4 (by positivity) (by positivity) (by norm_num) (by norm_num)
    (g.partial_model_endpoint_mass hd T labels samples selector S q z hqnorm).1
    (g.partial_model_endpoint_mass hd T labels samples selector S v z hvnorm).1
    x y hrowQ hrowV

end RegularGraph
end LocalLaw
