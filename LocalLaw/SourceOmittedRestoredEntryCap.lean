import LocalLaw.ActualOmittedRestoredEntryCap
import LocalLaw.CanonicalOmittedIdentification

/-! # Fixed entry caps for actual NEW local models after retained-B deletion -/

open Filter
noncomputable section
namespace LocalLaw
local instance sourceOmittedEntryCapDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace RegularGraph
theorem eventually_source_omitted_restored_entry_cap (a b d : ℕ)(c β B C1 : ℝ)
    (ha : 12≤a)(hb : 25*a≤b)(hd : 3≤d)(hc : 0<c)(hβ : 0<β)(hβc : β≤c/32)(hC1 : 1≤C1) :
    ∀ᶠ N:ℕ in atTop,∀(g : RegularGraph N d)(o : Fin N)(z q : ℂ),
      0<z.im → ‖z‖≤B → Real.log (N:ℝ)^b/(N:ℝ)≤z.im → 0≤q.im →
      ‖q-semicircleRoot z‖≤C1*scalarScale (spectralScale z)
        (graphPaperError a d N (logarithmicRadius β d N) z) →
      (∀v,graphBallExcess g.graph v (logarithmicRadius (c/4) d N)≤finiteOmega d) →
      ∀{ι:Type}[Fintype ι]
      (labels : ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples : LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (x y : ((graphBallVertices g.graph o (actualCavityDepth a d N z-1))ᶜ:Set (Fin N))),
      let T := graphBallVertices g.graph o (actualCavityDepth a d N z-1)
      let selector := logarithmicRadius (c/4) d N/4
      let r := effectiveModelRadius a d N β
      let s := g.admissibleState T labels samples
      ∀S:Set (Tᶜ:Set (Fin N)),S⊆s.twoTargetEndpointVertices selector r x y →
        let Bi:=s.partialFirstRemovedSet selector S
      let new:=(g.labelledResampledGraph T labels samples selector).deficient.delete T
      ∀i j:(Biᶜ:Set S),‖((new.restrict S).delete Bi).extensionGreen q z i j‖≤omittedRestoredEntryCap d B C1 := by
  filter_upwards [eventually_source_omitted_leaf_inputs a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_source_omitted_kept_control a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_source_formal_diagonal_bounds a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_sourceObservationBounds a b d c β B C1 ha hb hd hc hβ hβc hC1,
    eventually_paperError_small a b d β ha hb hd hβ]
    with N hinputs hcontrol hformal hnum hpaper
  intro g o z q hz hzB hfloor hq hprior hballs ι _ labels samples x y
  dsimp only
  let T:=graphBallVertices g.graph o (actualCavityDepth a d N z-1)
  let selector:=logarithmicRadius (c/4) d N/4
  let r:=effectiveModelRadius a d N β
  let s:=g.admissibleState T labels samples
  intro S hS
  let Bi:=s.partialFirstRemovedSet selector S
  let new:=(g.labelledResampledGraph T labels samples selector).deficient.delete T
  let e:=restrictionDeletionGraphIso new.graph S (s.selectedFirstSet selector) Bi (fun _=>Iff.rfl)
  letI:DecidableEq (s.OmittedCore selector S):=fun a b=>Classical.propDecidable (a=b)
  have hi:=hinputs g o z q hz hzB hfloor hq hprior hballs labels samples x y S hS
  have hc':=hcontrol g o z q hz hzB hfloor hq hprior hballs labels samples x y S hS
  have hf:=hformal z q hz hzB hfloor hprior
  have num:=hnum z hz hfloor
  let L:=Real.log (N:ℝ)
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  have hL:0<L:=by linarith [num.log_one]
  have hcap:ε*L^(4*a)≤1:=
    (le_div_iff₀ (pow_pos hL (4*a))).mp (by simpa only [one_div] using hpaper z hz hfloor)
  have hε1:ε≤1:=by
    have hp:1≤L^(4*a):=one_le_pow₀ num.log_one
    nlinarith only [hcap,hp,num.error_nonnegative]
  have hecap:=g.actual_omitted_restored_entry_cap hd T labels samples selector r S q z B C1
    (omittedCompletionObservationLogCap d β) L ε hz hq hf.2.1 hf.2.2.2.2.2 hL.le num.error_nonnegative hε1 hi hc'
  intro i j
  have hh:=hecap (e i) (e j)
  have he:=congrArg (fun P=>P i j) (g.canonical_omitted_restored_Green T labels samples selector S q z)
  change (g.omittedKeptRestoredModel T labels samples selector S).extensionGreen q z (e i) (e j)=
    ((new.restrict S).delete Bi).extensionGreen q z i j at he
  rw [he] at hh
  exact hh

end RegularGraph
end LocalLaw
