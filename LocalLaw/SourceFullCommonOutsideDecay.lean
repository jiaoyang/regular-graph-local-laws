import LocalLaw.SourceRegionalEntireDecay
import LocalLaw.FullRegionSupport

/-! # Actual common full-region exterior decay at arbitrary ambient targets

Every outside vertex of the literal common full model is allowed, including
cut vertices omitted by the local pair. The proof uses one old outside host;
no new model-class or enlarged-region hypothesis is introduced.
-/

open Filter
noncomputable section
set_option maxHeartbeats 1500000
namespace LocalLaw
local instance sourceFullCommonOutsideDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace RegularGraph

theorem eventually_source_full_common_outside_decay (a b d:ℕ)(c β Bcap C1:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hc:0<c)(hβ:0<β)(hβc:β≤c/32)(hC1:1≤C1) :
    ∀ᶠ N:ℕ in atTop,∀(g:RegularGraph N d)(o:Fin N)(z q:ℂ),
      0<z.im→‖z‖≤Bcap→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→0≤q.im→
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
      let S0:=s.fullSliceOutside (s.fullTwoTargetVertices selector r x y)
      let M:=((g.labelledResampledGraph T labels samples selector).deficient.delete T).restrict S0
      ∀(u v:S0)(h:ℕ),((2*h+2:ℕ):ℕ∞)≤(s.fullResample selector).graph.edist u.val.val v.val.val→
        ‖M.extensionGreen q z u v‖≤sourceRegionalEntireLeading d β Bcap C1*Real.log (N:ℝ)*physicalTransfer d z^h+
          sourceRegionalEntireError d β Bcap C1*Real.log (N:ℝ)*graphPaperError a d N (logarithmicRadius β d N) z := by
  filter_upwards [eventually_source_regional_entire_decay a b d c β Bcap C1 ha hb hd hc hβ hβc hC1,
    eventually_actual_inner_complement_nonempty a d (by omega) hd]
    with N hentire hnonempty
  intro g o z q hz hzB hfloor hq hprior hballs ι _ labels samples x y
  dsimp only
  let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
  let selector:=logarithmicRadius (c/4) d N/4
  let r:=effectiveModelRadius a d N β
  let s:=g.admissibleState T labels samples
  let S0:=s.fullSliceOutside (s.fullTwoTargetVertices selector r x y)
  let M:=((g.labelledResampledGraph T labels samples selector).deficient.delete T).restrict S0
  let w:(Tᶜ:Set (Fin N)):=Classical.choice (hnonempty g o z)
  let px:=s.outsideReplacement w x
  let py:=s.outsideReplacement w y
  have hS:S0⊆s.twoTargetEndpointVertices selector r px py:=s.fullTwoTarget_outside_subset_replacements selector r w x y
  have hregion:(s.selectedFirstSet selector⊆S0 ∧
      ∀i:s.AdmissibleSampleIndex selector,s.admissibleBoundaryVertex selector i∈S0) ∨
      Nat.card (s.partialFirstRemovedSet selector S0)≤2:=
    Or.inl ⟨s.selectedFirstSet_subset_fullRegion selector r x y,
      s.admissibleBoundaryVertex_mem_fullRegion selector r x y⟩
  have hh:=hentire g o z q hz hzB hfloor hq hprior hballs labels samples px py S0 hS hregion
  intro u v h hfar
  have hdist:((2*h+2:ℕ):ℕ∞)≤M.graph.edist u v:=
    hfar.trans ((ambient_edist_le_induced_edist (s.fullResample selector).graph Tᶜ u.val v.val).trans
      (graphHom_edist_le (SimpleGraph.Embedding.induce (G:=outsideGraph (s.fullResample selector).graph T) S0).toHom u v))
  exact hh u v h hdist

end RegularGraph
end LocalLaw
