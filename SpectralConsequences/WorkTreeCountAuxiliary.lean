import SpectralConsequences.SourceLargePatchProbability

/-! A second, smaller count auxiliary preserves the ORIGINAL work-event
bad-count threshold after switching. Its complement has every polynomial tail. -/
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance workTreeCountAuxiliaryDecidable (p:Prop):Decidable p:=Classical.propDecidable p

def WorkTreeCountAux {N d:ℕ}(cAux δ:ℝ)(g:LocalLaw.RegularGraph N d):Prop:=
  (nonTreeCenters g.graph (logarithmicRadius (cAux/16) d N)).card≤⌊(N:ℝ)^δ⌋₊

theorem eventually_workTreeCountAux_failure (d p:ℕ)(cAux δ:ℝ)
    (hd:3≤d)(hc:0≤cAux)(hδ:3*cAux/16<δ):
    ∀ᶠ N:ℕ in Filter.atTop,
      eventMass (LocalLaw.RegularGraph.weight (N:=N) (d:=d))
        (fun g=>¬WorkTreeCountAux cAux δ g)≤1/(N:ℝ)^p:=by
  filter_upwards [eventually_universal_badCenter_probability d 0 p (cAux/4) δ hd (by positivity) (by linarith)]
    with N hprob
  have hsub:∀g:LocalLaw.RegularGraph N d,¬WorkTreeCountAux cAux δ g→
      (N:ℝ)^δ<((nonTreeCenters g.graph (logarithmicRadius ((cAux/4)/4) d N+0)).card:ℝ):=by
    intro g hg
    apply lt_of_not_ge
    intro hle
    apply hg
    rw [show (cAux/4)/4=cAux/16 by ring,Nat.add_zero] at hle
    exact (Nat.le_floor_iff (Real.rpow_nonneg (Nat.cast_nonneg N) δ)).mpr hle
  exact (eventMass_mono LocalLaw.RegularGraph.weight LocalLaw.RegularGraph.weight_nonnegative hsub).trans hprob

theorem eventually_two_floor_rpow_le (δ c:ℝ)(hδ:δ<c):
    ∀ᶠ N:ℕ in Filter.atTop,2*⌊(N:ℝ)^δ⌋₊≤⌊(N:ℝ)^c⌋₊:=by
  filter_upwards [eventually_const_mul_log_rpow_le 2 0 (c-δ) (by linarith),
    Filter.eventually_ge_atTop 1] with N hnum hN
  have hn:0<(N:ℝ):=Nat.cast_pos.mpr (by omega)
  have htwo:2≤(N:ℝ)^(c-δ):=by simpa only [Real.rpow_zero,mul_one] using hnum
  apply (Nat.le_floor_iff (Real.rpow_nonneg hn.le c)).mpr
  calc
    ((2*⌊(N:ℝ)^δ⌋₊:ℕ):ℝ)=2*(⌊(N:ℝ)^δ⌋₊:ℝ):=by push_cast;ring
    _≤2*(N:ℝ)^δ:=mul_le_mul_of_nonneg_left (Nat.floor_le (Real.rpow_nonneg hn.le δ)) (by norm_num)
    _≤(N:ℝ)^(c-δ)*(N:ℝ)^δ:=mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hn.le δ)
    _=(N:ℝ)^c:=by rw [←Real.rpow_add hn];congr 1;ring

namespace RegularGraph

/-- The original work structural event uses badCount=floor N^(cAux/4),
not the much larger exponent used for rare sampled tree patches. -/
theorem eventually_source_original_work_bad_count (a d:ℕ)(cAux δ:ℝ)
    (ha:0<a)(hd:3≤d)(hc:0<cAux)(hδ:3*cAux/16<δ)(hδ1:δ<cAux/4):
    ∀ᶠ N:ℕ in Filter.atTop,∀(g:LocalLaw.RegularGraph N d)(o:Fin N)(z:ℂ),
      let ell:=actualCavityDepth a d N z-1
      let R:=logarithmicRadius (cAux/16) d N
      WorkTreeCountAux cAux δ g→∀{ι:Type*}[Fintype ι]
      (boundary:ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
      (S:LocalSamplingFiber g.graph (graphBallVertices g.graph o ell)),
      (nonTreeCenters ((g.admissibleState (graphBallVertices g.graph o ell) boundary S).fullResample (R/4)).graph R).card≤
        ⌊(N:ℝ)^(cAux/4)⌋₊:=by
  have hdepth:=(lowerLogLogRadius_tendsto a d ha hd).eventually (Filter.eventually_ge_atTop 4)
  filter_upwards [LocalLaw.RegularGraph.eventually_resampling_badCenter_cost a d (cAux/4) δ hd (by positivity) (by linarith),
    hdepth,eventually_two_floor_rpow_le δ (cAux/4) hδ1] with N hcost hdepth hfloor
  intro g o z
  dsimp only
  let ell:=actualCavityDepth a d N z-1
  let R:=logarithmicRadius (cAux/16) d N
  have hell:ell≤doubleLogRadius a d N:=(actualCavityDepth_radius_bounds a d N z hdepth).2
  intro haux ι _ boundary S
  let s:=g.admissibleState (graphBallVertices g.graph o ell) boundary S
  have hbudget:=hcost g o ell hell
  rw [show (cAux/4)/4=cAux/16 by ring] at hbudget
  exact (s.fullResample_badCount_twice (R/4) d R _ hd (fun v=>(g.regular v).le) haux hbudget).trans hfloor

end RegularGraph
end SpectralConsequences
#print axioms SpectralConsequences.eventually_workTreeCountAux_failure
#print axioms SpectralConsequences.RegularGraph.eventually_source_original_work_bad_count
