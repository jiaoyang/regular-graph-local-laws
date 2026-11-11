import LocalLaw.FullOutsideAugmentation
import LocalLaw.EffectiveModelRadius
import LocalLaw.SourceFormalKernelBounds

/-! # The exterior comparison consumed by the full near-cavity lift

This contract names literal outside slices and their actual inverse entries.
Its source proof is a separate deterministic resampling estimate.
-/

noncomputable section
namespace LocalLaw
local instance sourceFullExteriorFamilyDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace LabelledResamplingState
variable {V:Type}{T:Set V}{ι:Type}[Fintype ι]

def fullPairOutsideEmbedding (s:LabelledResamplingState V T ι)(selector r:ℕ)(x y:V) :
    s.fullSliceOutside (pairBallVertices (s.fullResample selector).graph x y r)↪
      s.fullSliceOutside (s.fullTwoTargetVertices selector r x y) where
  toFun u:=⟨u.val,s.switched_full_pair_subset_old_augmentation selector r x y u.property⟩
  inj':=by
    intro u v h
    exact Subtype.ext (congrArg (fun w:s.fullSliceOutside (s.fullTwoTargetVertices selector r x y)=>w.val) h)

end LabelledResamplingState

def SourceFullExteriorComparisonFamily (a b d:ℕ)(c β B C1:ℝ):Prop:=
  ∃K:ℝ,0≤K ∧ ∀ᶠ N:ℕ in Filter.atTop,∀(g:RegularGraph N d)(o:Fin N)(z q:ℂ),
    0<z.im→‖z‖≤B→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→0≤q.im→
    ‖q-semicircleRoot z‖≤C1*scalarScale (spectralScale z)
      (graphPaperError a d N (logarithmicRadius β d N) z)→
    (∀v,graphBallExcess g.graph v (logarithmicRadius (c/4) d N)≤finiteOmega d)→
    ∀{ι:Type}[Fintype ι]
    (labels:ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
    (samples:LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
    (x y:Fin N),
    let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
    let selector:=logarithmicRadius (c/4) d N/4
    let r:=effectiveModelRadius a d N β
    let s:=g.admissibleState T labels samples
    let A:=s.fullSliceOutside (s.fullTwoTargetVertices selector r x y)
    let S:=s.fullSliceOutside (pairBallVertices (s.fullResample selector).graph x y r)
    let e:=s.fullPairOutsideEmbedding selector r x y
    let new:=(g.labelledResampledGraph T labels samples selector).deficient.delete T
    let mass:ℝ:=Nat.card (BoundaryOrientedEdge g.graph T)
    ∀loss:ℕ,loss≤r/2→∀u v:S,
      ((s.fullResample selector).graph.edist x u.val.val≤(loss:ℕ∞) ∨
        (s.fullResample selector).graph.edist y u.val.val≤(loss:ℕ∞))→
      ((s.fullResample selector).graph.edist x v.val.val≤(loss:ℕ∞) ∨
        (s.fullResample selector).graph.edist y v.val.val≤(loss:ℕ∞))→
      ‖(new.restrict A).extensionGreen q z (e u) (e v)-(new.restrict S).extensionGreen q z u v‖≤
        K*Real.log (N:ℝ)*graphPaperError a d N (logarithmicRadius β d N) z+
          K*(mass+1)*Real.log (N:ℝ)^4*physicalTransfer d z^(2*(r-loss))

end LocalLaw
