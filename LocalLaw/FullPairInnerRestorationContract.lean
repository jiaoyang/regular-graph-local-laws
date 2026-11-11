import LocalLaw.PartialInnerAmbient

/-! A named actual full-pair inner-restoration estimate. -/
noncomputable section
namespace LocalLaw.RegularGraph
local instance fullPairInnerRestorationContractDecidable (p:Prop):Decidable p:=Classical.propDecidable p
variable {N d:ℕ}

def FullPairInnerRestoredAt (h:RegularGraph N d)(T:Set (Fin N))(r:ℕ)(z q:ℂ)
    (x y:Fin N)(hx:x∉T)(hy:y∉T)(δ:ℝ):Prop:=
  let S:=pairBallVertices h.graph x y r
  let K:Set (Tᶜ:Set (Fin N)):={v|v.val∈S}
  let xl:K:=⟨⟨x,hx⟩,Or.inl (center_mem_graphBall _ _ _)⟩
  let yl:K:=⟨⟨y,hy⟩,Or.inr (center_mem_graphBall _ _ _)⟩
  let lower:=(h.deficient.partialInnerAmbient T S).restrict K
  ‖h.P r z q x y-lower.extensionGreen q z xl yl‖≤δ

def FullPairQuarterFarInnerRestoredAt (h:RegularGraph N d)(T:Set (Fin N))(r:ℕ)(z q:ℂ)
    (x y:Fin N)(hx:x∉T)(hy:y∉T)(δ:ℝ):Prop:=
  (∀t:T,((r/4:ℕ):ℕ∞)<h.graph.edist x t.val ∧ ((r/4:ℕ):ℕ∞)<h.graph.edist y t.val)→
    h.FullPairInnerRestoredAt T r z q x y hx hy δ

end LocalLaw.RegularGraph
