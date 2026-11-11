import LocalLaw.SourceFullFarInnerRestoration

/-! Actual common full-region restoration at its two distinguished targets. -/
noncomputable section
namespace LocalLaw.RegularGraph
local instance fullCommonInnerContractDecidable (p:Prop):Decidable p:=Classical.propDecidable p
variable {N d:ℕ}{ι:Type}[Fintype ι]

def FullCommonInnerRestoredAt (g:RegularGraph N d)(T:Set (Fin N))
    (labels:ι≃BoundaryOrientedEdge g.graph T)(samples:LocalSamplingFiber g.graph T)
    (selector r:ℕ)(z q:ℂ)(x y:Fin N)(hx:x∉T)(hy:y∉T)(δ:ℝ):Prop:=
  let s:=g.admissibleState T labels samples
  let h:=g.labelledResampledGraph T labels samples selector
  let S:=s.fullTwoTargetVertices selector r x y
  let K:=s.fullSliceOutside S
  let xS:S:=twoBallLeft g.graph (filledExteriorVertices T (s.endpointModelVertices selector r)) x y r
  let yS:S:=twoBallRight g.graph (filledExteriorVertices T (s.endpointModelVertices selector r)) x y r
  let xl:K:=⟨⟨x,hx⟩,xS.property⟩
  let yl:K:=⟨⟨y,hy⟩,yS.property⟩
  ‖(h.deficient.restrict S).extensionGreen q z xS yS-
    ((h.deficient.delete T).restrict K).extensionGreen q z xl yl‖≤δ

def FullCommonQuarterFarInnerRestoredAt (g:RegularGraph N d)(T:Set (Fin N))
    (labels:ι≃BoundaryOrientedEdge g.graph T)(samples:LocalSamplingFiber g.graph T)
    (selector r:ℕ)(z q:ℂ)(x y:Fin N)(hx:x∉T)(hy:y∉T)(δ:ℝ):Prop:=
  (∀t:T,((r/4:ℕ):ℕ∞)<(g.labelledResampledGraph T labels samples selector).graph.edist x t.val ∧
    ((r/4:ℕ):ℕ∞)<(g.labelledResampledGraph T labels samples selector).graph.edist y t.val)→
      g.FullCommonInnerRestoredAt T labels samples selector r z q x y hx hy δ

end LocalLaw.RegularGraph
