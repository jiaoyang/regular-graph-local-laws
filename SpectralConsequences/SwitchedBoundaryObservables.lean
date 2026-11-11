import SpectralConsequences.ActualTwoSampleExpansion
import SpectralConsequences.TreeBoundaryCount
import SpectralConsequences.SwitchedTreeBoundaryBlock

/-! # The actual switched boundary observable and its two-sample leading term -/
open Filter
noncomputable section
set_option maxHeartbeats 2200000
namespace SpectralConsequences
open LocalLaw
local instance switchedBoundaryObservablesDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace RegularGraph
variable {N d:ℕ} {T:Set (Fin N)} {ι:Type} [Fintype ι]

def switchedBoundaryEntry (g:LocalLaw.RegularGraph N d)
    (labels:ι≃BoundaryOrientedEdge g.graph T) (S:LocalSamplingFiber g.graph T)
    (selector:ℕ) (z:ℂ) (j k:ι) : ℂ :=
  let s:=g.admissibleState T labels S
  g.sourceEndpointT T labels S selector z
    (s.endpointFinalBoundaryRoot selector j) (s.endpointFinalBoundaryRoot selector k)

def sampledBoundaryLeading (g:LocalLaw.RegularGraph N d)
    (labels:ι≃BoundaryOrientedEdge g.graph T) (S:LocalSamplingFiber g.graph T)
    (z:ℂ) (j k:ι) : ℂ :=
  let e:=S (labels j)
  let f:=S (labels k)
  let A:=treeEdgeWeight d*g.Q z
  g.G z e.val.2 f.val.2+A*g.G z e.val.1 f.val.2+
    A*g.G z e.val.2 f.val.1+A^2*g.G z e.val.1 f.val.1

theorem switchedBoundaryEntry_accepted (g:LocalLaw.RegularGraph N d)
    (labels:ι≃BoundaryOrientedEdge g.graph T) (S:LocalSamplingFiber g.graph T)
    (selector:ℕ) (z:ℂ) (j k:ι)
    (hj:(g.admissibleState T labels S).Eligible selector j)
    (hk:(g.admissibleState T labels S).Eligible selector k) :
    switchedBoundaryEntry g labels S selector z j k=
      ((g.labelledResampledGraph T labels S selector).deficient.delete T).G z
        ((g.admissibleState T labels S).admissibleSecondVertex selector ⟨j,hj⟩)
        ((g.admissibleState T labels S).admissibleSecondVertex selector ⟨k,hk⟩) := by
  simp only [switchedBoundaryEntry,LocalLaw.RegularGraph.sourceEndpointT,Matrix.submatrix_apply,
    LabelledResamplingState.endpointFinalBoundaryRoot,dif_pos hj,dif_pos hk]
  rfl

theorem eventually_source_boundary_offdiag_pointwise (a b d:ℕ) (c β B C1:ℝ)
    (ha:12≤a) (hb:25*a≤b) (hd:3≤d) (hc:0<c) (hβ:0<β) (hβc:β≤c/32)
    (hB:0≤B) (hC1:1≤C1) :
    ∀ᶠ N:ℕ in atTop,∀(g:LocalLaw.RegularGraph N d)(o:Fin N)(z:ℂ),
      0<z.im → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → ‖z‖≤B →∀Cq badCount:ℕ,
      g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (finiteOmega d) badCount z →
      g.SourceOmegaPlusWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (actualCavityDepth a d N z-1)
        (finiteOmega d) Cq badCount C1 o z →
      (graphBall g.graph o (actualCavityDepth a d N z-1)).IsTree →
      ∀{ι:Type}[Fintype ι]
      (labels:ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (S:LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1))),
      let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let selector:=logarithmicRadius (c/4) d N/4
      let s:=g.admissibleState T labels S
      ∀j k:ι,j≠k→s.Eligible selector j→s.Eligible selector k→
      ‖switchedBoundaryEntry g labels S selector z j k-sampledBoundaryLeading g labels S z j k‖≤
        (2*sourceSelectedMinorConstant d B C1)*(Nat.card (BoundaryOrientedEdge g.graph T):ℝ)*
          (g.sourcePrime a (logarithmicRadius β d N) z)^2+
        twoSampleQuadraticConstant d β B*Real.log (N:ℝ)^2*
          (graphPaperError a d N (logarithmicRadius β d N) z)^2 := by
  filter_upwards [eventually_source_tree_sampled_minor_comparison a b d c β B C1
      ha hb hd hc hβ hβc hB hC1,
    eventually_actual_two_sample_expansion a b d c β B ha hb hd hc hβ hβc hB]
    with N hminor hquad
  intro g o z hz hfloor hzB Cq badCount hold hplus hTree ι _ labels S
  dsimp only
  let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
  let selector:=logarithmicRadius (c/4) d N/4
  let s:=g.admissibleState T labels S
  intro j k hjk hj hk
  let i:s.AdmissibleSampleIndex selector:=⟨j,hj⟩
  let i':s.AdmissibleSampleIndex selector:=⟨k,hk⟩
  have hii':i≠i':=fun he=>hjk (congrArg Subtype.val he)
  have hm:=hminor g o z hz hfloor hzB Cq badCount hold hplus labels S hTree i i'
  have hq:=hquad g o z hz hzB hfloor badCount hold labels S i i' hii'
  change ‖sampledDoubleMinor g labels S selector z i i'-sampledBoundaryLeading g labels S z j k‖≤_ at hq
  rw [switchedBoundaryEntry_accepted g labels S selector z j k hj hk]
  exact (norm_sub_le_norm_sub_add_norm_sub _ (sampledDoubleMinor g labels S selector z i i') _).trans
    (add_le_add hm hq)

end RegularGraph
end SpectralConsequences
