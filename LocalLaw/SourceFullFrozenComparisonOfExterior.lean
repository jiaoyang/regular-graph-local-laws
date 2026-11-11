import LocalLaw.SourceFullNearComparisonOfExterior
import LocalLaw.SourceFullFarExteriorComparisonOfExterior
import LocalLaw.SourceFullCommonFarRestoration
import LocalLaw.SourceFullCommonSurgery
import LocalLaw.SourceOmittedInnerComparison

/-! The full physical frozen comparison follows from the actual exterior family.
The close and far inner restorations, model identities and all budgets are derived. -/
open Filter
noncomputable section
namespace LocalLaw
local instance sourceFullFrozenExteriorDecidable (p:Prop):Decidable p:=Classical.propDecidable p
set_option maxHeartbeats 1800000
namespace RegularGraph

theorem source_full_frozen_comparison_of_exterior (a b d:ℕ)(c β B:ℝ)
    (ha:12≤a)(hb:25*a≤b)(hd:3≤d)(hc:0<c)(hβ:0<β)(hβc:β≤c/32)
    (hExterior:SourceFullExteriorComparisonFamily a b d c β B 1):
    ∃D:ℝ,1≤D ∧ ∀ᶠ N:ℕ in atTop,∀(g:RegularGraph N d)(o:Fin N)(z:ℂ),
      0<z.im→‖z‖≤B→Real.log (N:ℝ)^b/(N:ℝ)≤z.im→∀badCount:ℕ,
      g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
        (logarithmicRadius (c/4) d N) (finiteOmega d) badCount z→
      ∀{ι:Type}[Fintype ι]
      (labels:ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples:LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (x y:Fin N),
      let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let h:=g.labelledResampledGraph T labels samples (logarithmicRadius (c/4) d N/4)
      ‖h.G z x y-h.P (effectiveModelRadius a d N β) z (g.Q z) x y‖≤D/Real.log (N:ℝ):=by
  obtain ⟨Dn,hDn,hnear⟩:=source_full_near_comparison_of_exterior a b d c β B 1 ha hb hd hc hβ hβc le_rfl hExterior
  obtain ⟨Df,hDf,hext⟩:=source_full_far_exterior_comparison_of_exterior a b d c β B 1 ha hb hd hβ hExterior
  refine ⟨Dn+Df+4,by linarith,?_⟩
  filter_upwards [hnear,hext,
    eventually_source_full_common_far_inner_restoration a b d c β B 1 ha hb hd hc hβ hβc le_rfl,
    eventually_source_full_far_inner_restoration a b d c β B 1 ha hb hd hc hβ hβc le_rfl,
    eventually_source_omitted_inner_comparison a b d c β B 1 ha hb hd hc hβ hβc le_rfl,
    eventually_source_full_common_surgery a b d c β B ha hb hd hc hβ hβc,
    eventually_source_quarter_cut_dichotomy a d β (by omega) hd hβ,
    eventually_log_ge_nat 1] with N hNear hExt hCommon hPair hNorm hPhysical hQuarter hLog
  intro g o z hz hzB hfloor badCount hsource ι _ labels samples x y
  dsimp only
  let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
  let selector:=logarithmicRadius (c/4) d N/4
  let r:=effectiveModelRadius a d N β
  let s:=g.admissibleState T labels samples
  let h:=g.labelledResampledGraph T labels samples selector
  let S0:=s.fullTwoTargetVertices selector r x y
  let x0:S0:=twoBallLeft g.graph (filledExteriorVertices T (s.endpointModelVertices selector r)) x y r
  let y0:S0:=twoBallRight g.graph (filledExteriorVertices T (s.endpointModelVertices selector r)) x y r
  let C:ℂ:=(h.deficient.restrict S0).extensionGreen (g.Q z) z x0 y0
  let P:ℂ:=h.P r z (g.Q z) x y
  let L:=Real.log (N:ℝ)
  have hL0:0≤L:=by dsimp only[L];linarith
  have hprior:‖g.Q z-semicircleRoot z‖≤1*scalarScale (spectralScale z)
      (graphPaperError a d N (logarithmicRadius β d N) z):=by
    simpa only[one_mul] using hsource.2.1
  have hq:0≤(g.Q z).im:=g.Q_im_nonnegative z hz
  have hPhysical':‖h.G z x y-C‖≤1/L:=hPhysical g o z hz hzB hfloor badCount hsource labels samples x y
  have hModel:‖C-P‖≤(Dn+Df+3)/L:=by
    rcases (hQuarter g o z labels samples selector x y).2.2 with hclose|hfar
    · have hh:=hNear g o z (g.Q z) hz hzB hfloor hq hprior hsource.1.1 labels samples x y hclose.1
      exact hh.trans (div_le_div_of_nonneg_right (by linarith) hL0)
    · obtain ⟨hx,hy,hfar⟩:=hfar
      let S1:=s.fullSliceOutside (pairBallVertices h.graph x y r)
      let e:=s.fullPairOutsideEmbedding selector r x y
      let xl:S1:=⟨⟨x,hx⟩,Or.inl (center_mem_graphBall _ _ _)⟩
      let yl:S1:=⟨⟨y,hy⟩,Or.inr (center_mem_graphBall _ _ _)⟩
      let U0:ℂ:=((h.deficient.delete T).restrict (s.fullSliceOutside S0)).extensionGreen (g.Q z) z (e xl) (e yl)
      let U1:ℂ:=((h.deficient.delete T).restrict S1).extensionGreen (g.Q z) z xl yl
      let V:ℂ:=((h.deficient.partialInnerAmbient T (pairBallVertices h.graph x y r)).restrict S1).extensionGreen (g.Q z) z xl yl
      have hf:∀t:T,((r/4:ℕ):ℕ∞)<h.graph.edist x t.val ∧ ((r/4:ℕ):ℕ∞)<h.graph.edist y t.val:=
        fun t=>hfar t.val t.property
      have hc0:=hCommon g o z (g.Q z) hz hzB hfloor hq hprior hsource.1.1 labels samples x y hx hy
      change g.FullCommonQuarterFarInnerRestoredAt T labels samples selector r z (g.Q z) x y hx hy (1/L) at hc0
      have hc1:=hc0 hf
      change ‖C-U0‖≤1/L at hc1
      have he:=hExt g o z (g.Q z) hz hzB hfloor hq hprior hsource.1.1 labels samples x y hx hy
      change ‖U0-U1‖≤Df/L at he
      have hp:=hPair g o z (g.Q z) hz hzB hfloor hq hprior hsource.1.1 labels samples x y hx hy
      change h.FullPairQuarterFarInnerRestoredAt T r z (g.Q z) x y hx hy (1/L) at hp
      have hp':=hp hf
      change ‖P-V‖≤1/L at hp'
      have hn:=(hNorm g o z (g.Q z) hz hzB hfloor hq hprior hsource.1.1 labels samples x y hx hy).2
      change ‖U1-V‖≤1/L at hn
      have hnp:‖V-P‖≤1/L:=(norm_sub_rev V P).le.trans hp'
      have h1:‖C-U1‖≤1/L+Df/L:=
        (norm_sub_le_norm_sub_add_norm_sub C U0 U1).trans (add_le_add hc1 he)
      have h2:‖U1-P‖≤1/L+1/L:=
        (norm_sub_le_norm_sub_add_norm_sub U1 V P).trans (add_le_add hn hnp)
      have hh:‖C-P‖≤(Df+3)/L:=
        ((norm_sub_le_norm_sub_add_norm_sub C U1 P).trans (add_le_add h1 h2)).trans_eq (by ring)
      exact hh.trans (div_le_div_of_nonneg_right (by linarith) hL0)
  exact ((norm_sub_le_norm_sub_add_norm_sub (h.G z x y) C P).trans
    (add_le_add hPhysical' hModel)).trans_eq (by ring)

end RegularGraph
end LocalLaw
