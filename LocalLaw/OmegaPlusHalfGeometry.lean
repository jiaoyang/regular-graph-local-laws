import LocalLaw.OmegaPlusRejectionProbability
import LocalLaw.FullGeometricParameters
import LocalLaw.SourceResamplingStructural
import LocalLaw.GeometricKernelProbability
import LocalLaw.IndependentRadiusEvents
import LocalLaw.AdmissibleGreenBlock

/-! # Actual half-radius F1 data under the enlarged source event

Only the old half-radius excess bound and the literal doubled bad-center
count of structural-plus are used. The additional uniform occupancy input
for outside columns has a proved arbitrary-polynomial cost.
-/

noncomputable section
set_option maxHeartbeats 2400000
namespace LocalLaw
local instance omegaPlusHalfGeometryDecidable (p:Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph

theorem eventually_structuralPlus_halfGeometric_probability (a d p:ℕ) (c γ:ℝ)
    (hd:3≤d) (hc:0<c) (hc₁:c<1) (hγ:γ<1) :
    ∃q:ℕ,1≤q ∧ ∀ᶠ N:ℕ in Filter.atTop,∀(g:RegularGraph N d)(o:Fin N)(ell ω Cq:ℕ),
      ell≤doubleLogRadius a d N → g.SourceStructuralPlus (logarithmicRadius (c/4) d N) ω Cq ⌊(N:ℝ)^γ⌋₊ →
      eventMass (localSamplingWeight g.graph (graphBallVertices g.graph o ell)) (fun S=>
        ¬SourceFullGeometricGood g.graph o ell (logarithmicRadius (c/4) d N/2) Cq
          (q-1) (q-1) (2*q*(2*(q-1)+1)) (q-1) S)≤1/(N:ℝ)^p := by
  let γ':=(γ+1)/2
  have hγ':γ'<1:=by dsimp only [γ'];linarith
  have hgap:0<γ'-γ:=by dsimp only [γ'];linarith
  obtain ⟨q,hq,hnum⟩:=eventually_geometric_sampling_budget a d (p+1) c γ' hc₁ hγ'
  refine ⟨q,hq,?_⟩
  filter_upwards [hnum,eventually_resampling_ball_budget a d hd,
    eventually_resampling_radius_margin a d 4 4 (c/4) hd (by linarith),eventually_log_ge_nat 1,
    Filter.eventually_ge_atTop 8,eventually_const_mul_log_rpow_le 2 0 (γ'-γ) hgap]
    with N hnum hball hmargin hlog hN htwo
  intro g o ell ω Cq hell hstruct
  let R:=logarithmicRadius (c/4) d N
  let M:=R/2
  let T:=graphBallVertices g.graph o ell
  let μ:ℝ:=Nat.card (BoundaryOrientedEdge g.graph T)
  let V:ℝ:=(((d+1)*(d-1)^M:ℕ):ℝ)
  let b:ℕ:=2*⌊(N:ℝ)^γ⌋₊
  have hn:(0:ℝ)<N:=Nat.cast_pos.mpr (by omega)
  have hT:4*Nat.card T≤N:=by
    apply (Nat.mul_le_mul_left 4 ((g.ball_card_bound o ell).trans
      (Nat.pow_le_pow_right (by omega:0<d+1) hell))).trans hball
  have hfit:2*ell+2≤M:=by dsimp only [R,M];omega
  have hMR:M+1≤R:=by dsimp only [R,M];omega
  have hbad:(nonTreeCenters g.graph (M+1)).card≤b:=
    (Finset.card_le_card (nonTreeCenters_mono g.graph hMR)).trans hstruct.2.2
  have hμ:μ≤(d:ℝ)*((d:ℝ)+1)*Real.log (N:ℝ)^(2*a):=g.boundary_card_log_bound o a ell hd hlog hell
  have hV:V≤((d:ℝ)+1)*(N:ℝ)^(c/4):=by
    have hm:M≤R:=Nat.div_le_self _ _
    have hmono: (d+1)*(d-1)^M≤(d+1)*(d-1)^R:=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega:0<d-1) hm)
    have hp:=logarithmicRadius_power_bound (c/4) d N (by linarith) hd (by omega)
    apply (Nat.cast_le.mpr hmono).trans
    dsimp only [R] at *
    push_cast
    exact mul_le_mul_of_nonneg_left hp (by positivity)
  have hb:(b:ℝ)≤(N:ℝ)^γ':=by
    have hfl:=Nat.floor_le (Real.rpow_nonneg hn.le γ)
    have htwo':(2:ℝ)≤(N:ℝ)^(γ'-γ):=by simpa using htwo
    calc
      (b:ℝ)≤2*(N:ℝ)^γ:=by dsimp only [b];push_cast;nlinarith
      _≤(N:ℝ)^(γ'-γ)*(N:ℝ)^γ:=mul_le_mul_of_nonneg_right htwo' (Real.rpow_nonneg hn.le _)
      _=(N:ℝ)^γ':=by rw [←Real.rpow_add hn];congr 1;ring
  have hprob:=g.localSampling_sourceFullGeometricGood_failure o ell M Cq (q-1) (q-1) q (q-1) b
    (by omega) hd hT hfit (hstruct.2.1 o) hbad
  have hexp:q-1+1=q:=Nat.sub_add_cancel hq
  rw [hexp] at hprob
  have hbudget:=hnum μ V (b:ℝ) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hμ hV hb
  have hnonneg:0≤2*(N:ℝ)*(μ*(4*V/N))^q+(μ^2*(8*V/N))^q+(μ*(4*(b:ℝ)/N))^q:=by positivity
  have hdouble:2*(N:ℝ)*(μ*(4*V/N))^q+2*(4*μ^2*V/N)^q+(μ^2*(8*V/N))^q+(μ*(4*(b:ℝ)/N))^q≤8/(N:ℝ)^(p+1):=by
    calc
      _≤2*(2*(N:ℝ)*(μ*(4*V/N))^q+(4*μ^2*V/N)^q+(μ^2*(8*V/N))^q+(μ*(4*(b:ℝ)/N))^q):=by linarith only [hnonneg]
      _≤2*(4/(N:ℝ)^(p+1)):=mul_le_mul_of_nonneg_left hbudget (by norm_num)
      _=_:=by ring
  apply (hprob.trans hdouble).trans
  apply (div_le_div_iff₀ (pow_pos hn _) (pow_pos hn _)).mpr
  rw [pow_succ]
  nlinarith [mul_le_mul_of_nonneg_right (show (8:ℝ)≤N by exact_mod_cast hN) (pow_nonneg hn.le p)]


def halfGeometryOccupancyConstant (Cq q:ℕ):ℕ:=
  resamplingTripleOccupancyConstant Cq (q-1) (q-1) (2*q*(2*(q-1)+1))

theorem halfGeometricGood_switched_occupancy {N d:ℕ} {ι:Type} [Fintype ι]
    (g:RegularGraph N d)(o:Fin N)(ell R Cq q:ℕ)
    (labels:ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
    (samples:LocalSamplingFiber g.graph (graphBallVertices g.graph o ell))
    (hgood:SourceFullGeometricGood g.graph o ell (R/2) Cq (q-1) (q-1) (2*q*(2*(q-1)+1)) (q-1) samples) :
    let s:=g.admissibleState (graphBallVertices g.graph o ell) labels samples
    ∀x:((graphBallVertices g.graph o ell)ᶜ:Set (Fin N)),
      (tripleNearIndices (s.fullResample (R/4)).graph (graphBallVertices g.graph o ell) (R/4)
        (s.fullResample (R/4)).samples x).card≤halfGeometryOccupancyConstant Cq q := by
  have hh:=g.sourceFullGood_labelledResampled_tripleNear o ell (R/4) (R/2) Cq (q-1) (q-1)
    (2*q*(2*(q-1)+1)) (q-1) labels samples hgood
  have hdiv:(R/2)/2=R/4:=by omega
  simpa only [hdiv,halfGeometryOccupancyConstant] using hh

end RegularGraph

def ballOmegaPlusHalfGeometricBad {N d:ℕ} (a Cq q:ℕ)(c:ℝ)(o:Fin N)(z:ℂ):BallLabelledSpace N d→Prop:=
  ballCanonicalSampleEvent o (actualCavityDepth a d N z-1) (fun g S=>
    ¬SourceFullGeometricGood g.graph o (actualCavityDepth a d N z-1) (logarithmicRadius (c/4) d N/2) Cq
      (q-1) (q-1) (2*q*(2*(q-1)+1)) (q-1) S)

theorem eventually_ballOmegaPlusHalfGeometricBad_probability (a d p:ℕ)(c γ:ℝ)
    (ha:0<a)(hd:3≤d)(hc:0<c)(hc₁:c<1)(hγ:γ<1):
    ∃q:ℕ,1≤q ∧ ∀ᶠ N:ℕ in Filter.atTop,∀(o:Fin N)(z:ℂ)(rModel rError Cq:ℕ)(C1:ℝ),
      eventMass (ballLabelledWeight N d o (actualCavityDepth a d N z-1)) (fun ξ=>
        (ballLabelledProject ξ).SourceOmegaPlusWithRadii a rModel rError (logarithmicRadius (c/4) d N)
          (actualCavityDepth a d N z-1) (finiteOmega d) Cq ⌊(N:ℝ)^γ⌋₊ C1 o z ∧
        ballOmegaPlusHalfGeometricBad a Cq q c o z ξ)≤1/(N:ℝ)^p:=by
  obtain ⟨q,hq,hprob⟩:=RegularGraph.eventually_structuralPlus_halfGeometric_probability a d p c γ hd hc hc₁ hγ
  have hdepth:=(lowerLogLogRadius_tendsto a d ha hd).eventually (Filter.eventually_ge_atTop 4)
  refine ⟨q,hq,?_⟩
  filter_upwards [hprob,hdepth] with N hprob hdepth
  intro o z rModel rError Cq C1
  let ell:=actualCavityDepth a d N z-1
  let A:RegularGraph N d→Prop:=fun g=>g.SourceOmegaPlusWithRadii a rModel rError
    (logarithmicRadius (c/4) d N) ell (finiteOmega d) Cq ⌊(N:ℝ)^γ⌋₊ C1 o z
  have hh:=ballCanonical_sample_failure_bound N d o ell A
    (fun g S=>¬SourceFullGeometricGood g.graph o ell (logarithmicRadius (c/4) d N/2) Cq
      (q-1) (q-1) (2*q*(2*(q-1)+1)) (q-1) S) (1/(N:ℝ)^p)
    (fun g hA=>hprob g o ell (finiteOmega d) Cq (actualCavityDepth_radius_bounds a d N z hdepth).2 hA.structural)
  have hmass:eventMass (RegularGraph.weight (N := N) (d := d)) A≤1:=finiteUniform_eventMass_le_one A
  exact hh.trans ((mul_le_mul_of_nonneg_left hmass (by positivity)).trans_eq (mul_one _))

end LocalLaw
