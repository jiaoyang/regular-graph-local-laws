import SpectralConsequences.LargePatchSampling
import LocalLaw.GeometricSamplingParameters

/-! A genuine polynomial gap for all-label radius-2R sampling. -/
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance largePatchParametersDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace RegularGraph

theorem eventually_allLargeSampleGood_failure (a d:ℕ)(c γ:ℝ)
    (hd:3≤d)(hc:0≤c)(hγc:c/2≤γ)(hγ:γ<1):
    ∀ᶠ N:ℕ in Filter.atTop,∀(g:LocalLaw.RegularGraph N d)(o:Fin N)(ell:ℕ),
      ell≤doubleLogRadius a d N→
      (nonTreeCenters g.graph (2*logarithmicRadius (c/4) d N+1)).card≤⌊(N:ℝ)^γ⌋₊→
      eventMass (localSamplingWeight g.graph (graphBallVertices g.graph o ell))
        (fun S=>¬AllLargeSampleGood g.graph (graphBallVertices g.graph o ell)
          (2*logarithmicRadius (c/4) d N) S)≤1/(N:ℝ)^((1-γ)/2):=by
  let C:=geometricSamplingConstant d
  have hC:0≤C:=by dsimp only [C,geometricSamplingConstant];positivity
  filter_upwards [eventually_resampling_ball_budget a d hd,
    eventually_const_mul_log_rpow_le (3*C) ((4*a:ℕ):ℝ) ((1-γ)/2) (by linarith),
    eventually_log_ge_nat 1,Filter.eventually_ge_atTop 2]
    with N hball hnum hlog hN
  intro g o ell hell hbad
  let T:=graphBallVertices g.graph o ell
  let R:=logarithmicRadius (c/4) d N
  let μ:ℝ:=Nat.card (BoundaryOrientedEdge g.graph T)
  let V:ℝ:=(((d+1)*(d-1)^(2*R):ℕ):ℝ)
  let b:ℕ:=⌊(N:ℝ)^γ⌋₊
  let gap:=1-γ
  let A:=C*Real.log (N:ℝ)^(4*a)/(N:ℝ)^gap
  have hNp:0<(N:ℝ):=Nat.cast_pos.mpr (by omega)
  have hN1:1≤(N:ℝ):=by exact_mod_cast (show 1≤N by omega)
  have hT:4*Nat.card T≤N:=by
    exact (Nat.mul_le_mul_left 4 ((g.ball_card_bound o ell).trans
      (Nat.pow_le_pow_right (by omega:0<d+1) hell))).trans hball
  have hμ:μ≤(d:ℝ)*((d:ℝ)+1)*Real.log (N:ℝ)^(2*a):=
    g.boundary_card_log_bound o a ell hd hlog hell
  have hV:V≤((d:ℝ)+1)*(N:ℝ)^(c/2):=by
    have hh:=logarithmicRadius_power_bound (c/4) d N (by linarith) hd (by omega)
    have hp:(((d-1:ℕ):ℝ)^(2*R))≤(N:ℝ)^(c/2):=by
      calc
        _=((((d-1:ℕ):ℝ)^R)^2):=by rw [←pow_mul];congr 1;omega
        _≤((N:ℝ)^(c/4))^2:=pow_le_pow_left₀ (by positivity) hh 2
        _=(N:ℝ)^(c/2):=by rw [←Real.rpow_natCast _ 2,←Real.rpow_mul hNp.le];congr 1;ring
    dsimp only [V]
    push_cast
    exact mul_le_mul_of_nonneg_left hp (by positivity)
  have hb:(b:ℝ)≤(N:ℝ)^γ:=Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) γ)
  have hbases:=geometric_sampling_bases (N:ℝ) (Real.log (N:ℝ)) μ V b a d (2*c) γ gap
    hN1 hlog (by dsimp only [μ];positivity) (by dsimp only [V];positivity)
    (Nat.cast_nonneg b) hμ (by convert hV using 2;ring) hb
    (by dsimp only [gap];linarith) (by dsimp only [gap];linarith)
  change _≤A ∧ _≤A ∧ _≤A ∧ _≤A at hbases
  have hprob:=localSampling_allLargeSampleGood_failure g T (by omega) hd hT (2*R) b hbad
  have hsum:12*μ^2*V/(N:ℝ)+4*μ*b/(N:ℝ)≤3*A:=by
    have hh:=add_le_add hbases.2.1 (add_le_add hbases.2.2.1 hbases.2.2.2)
    convert hh using 1 <;> ring
  have hsmall:3*C*Real.log (N:ℝ)^(4*a)≤(N:ℝ)^(gap/2):=by
    simpa only [Real.rpow_natCast] using hnum
  have hpow:(N:ℝ)^gap=(N:ℝ)^(gap/2)*(N:ℝ)^(gap/2):=by
    rw [←Real.rpow_add hNp]
    congr 1
    ring
  have htail:3*A≤1/(N:ℝ)^(gap/2):=by
    dsimp only [A]
    rw [←mul_div_assoc]
    apply (div_le_div_iff₀ (Real.rpow_pos_of_pos hNp gap) (Real.rpow_pos_of_pos hNp (gap/2))).mpr
    have hh:=mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg hNp.le (gap/2))
    rw [←hpow] at hh
    convert hh using 1 <;> ring
  exact hprob.trans (hsum.trans htail)

end RegularGraph
end SpectralConsequences
#print axioms SpectralConsequences.RegularGraph.eventually_allLargeSampleGood_failure
