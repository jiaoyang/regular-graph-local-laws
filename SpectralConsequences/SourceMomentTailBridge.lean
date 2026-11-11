import SpectralConsequences.SourceHighMomentBounds
import SpectralConsequences.PolynomialMomentMarkov
import SpectralConsequences.MomentExteriorScaleComparison
import SpectralConsequences.OriginalExteriorProbability

/-! Actual source high moments imply the two physical residual tails used
in the final exterior probability reduction. No trace/confinement estimate
is an input to this bridge. -/
open Filter
noncomputable section
set_option maxHeartbeats 1800000
namespace SpectralConsequences
open LocalLaw
local instance sourceMomentTailBridgeDecidable (p:Prop):Decidable p:=Classical.propDecidable p

theorem momentResidual_cavity_eq_physical {N d:ℕ}(a:ℕ)(g:RegularGraph N d)(z:ℂ):
    momentResidual true g (actualCavityDepth a d N z-1) z=physicalCavityFluctuation a g z:=by
  have hb:2≤baselineCavityDepth a d N:=by unfold baselineCavityDepth;omega
  have hn:baselineCavityDepth a d N≤actualCavityDepth a d N z:=
    (nonresonantDepth_bounds _ _).1
  have he:actualCavityDepth a d N z-1+1=actualCavityDepth a d N z:=by omega
  simp only [momentResidual,if_true,physicalCavityFluctuation,he]

theorem momentResidual_trace_eq_physical {N d:ℕ}(a:ℕ)(g:RegularGraph N d)(z:ℂ):
    momentResidual false g (actualCavityDepth a d N z-1) z=physicalTraceFluctuation a g z:=by
  simp only [momentResidual,Bool.false_eq_true,if_false,physicalTraceFluctuation]

theorem sourceExteriorFluctuationScale_positive (a d N:ℕ)(β γ:ℝ)(hd:3≤d)(hN:1≤N)
    (hL:1≤Real.log (N:ℝ))(hβ:0≤β)(z:ℂ)(hz:0≤z.im):
    0<sourceExteriorFluctuationScale a d N β γ z:=by
  let ε:=graphPaperError a d N (logarithmicRadius β d N) z
  have hNp:0<(N:ℝ):=Nat.cast_pos.mpr (by omega)
  have hε:0<ε:=lt_of_lt_of_le (inv_pos.mpr (Real.rpow_pos_of_pos hNp β))
    (graphPaperError_nominal_ge_inverse_power a d N β z hd hβ hN hL hz)
  have hLp:0<Real.log (N:ℝ):=by linarith
  have heprime:0 < inflatedPrime (Real.log (N:ℝ)) ε:=by unfold inflatedPrime;positivity
  have hk:0<((d-1:ℕ):ℝ):=Nat.cast_pos.mpr (by omega)
  unfold sourceExteriorFluctuationScale
  change 0<Real.sqrt ε*Real.sqrt _+((d-1:ℕ):ℝ)^(2*(actualCavityDepth a d N z-1))*
    (inflatedPrime (Real.log (N:ℝ)) ε)^2+inflatedPrime (Real.log (N:ℝ)) ε/(N:ℝ)^γ
  positivity

theorem source_high_moments_imply_exterior_tails (a b d:ℕ)(cOriginal β γ e:ℝ)
    (hd:3≤d)(hβ:0<β)(hβsmall:β≤1/128)(he:0<e)
    (hmom:SourceHighMomentBounds a b d (exteriorWorkParameter cOriginal) β
      (sourceExteriorProbabilityBound d)):
    ExteriorPhysicalResidualTails a d cOriginal β γ e 1 0:=by
  intro D
  obtain ⟨p,hp,horder⟩:=polynomial_moment_order e he (D+1)
  obtain ⟨C,hC,q,hMom⟩:=hmom p hp
  let B:=sourceExteriorProbabilityBound d
  let K:=sourceWardVarianceConstant d B
  let Ctot:=C*(K+1)
  let qtot:=q+2*a
  have hB:0≤B:=by
    have hs:2≤sourceSpectralBox d:=le_max_left _ _
    dsimp only [B,sourceExteriorProbabilityBound]
    positivity
  have hK:0≤K:=sourceWardVarianceConstant_nonnegative d B hd hB
  have hCtot:0≤Ctot:=by dsimp only [Ctot];positivity
  filter_upwards [hMom,eventually_polylog_moment_markov Ctot (qtot:ℝ) e hCtot he p (D+1) horder,
    eventually_exterior_source_parameters (a:ℝ) (b:ℝ) d β (sourceSpectralBox d) hd hβ hβsmall,
    eventually_log_ge_nat 1,eventually_ge_atTop 2]
    with N hMoment hMarkov num hL hN
  intro E hE
  let z:=exteriorSpectralPoint β N E
  let S:=sourceExteriorFluctuationScale a d N β γ z
  have hspec:=sourceExteriorMesh_spectral_bounds (a:ℝ) (b:ℝ) d N β num E hE
  have hz:0<z.im:=hspec.1
  have hzB:‖z‖≤B:=hspec.2.2.1.trans (by
    dsimp only [B,sourceExteriorProbabilityBound]
    have hh:0≤(d:ℝ):=Nat.cast_nonneg _
    linarith)
  have hfloor:Real.log (N:ℝ)^b/(N:ℝ)≤z.im:=by
    simpa only [Real.rpow_natCast] using hspec.2.1
  have hS:0<S:=sourceExteriorFluctuationScale_positive a d N β γ hd (by omega) hL hβ.le z hz.le
  have hcompare:sourceHighMomentScale a d N β B z≤(K+1)*Real.log (N:ℝ)^(2*a)*S:=
    source_moment_scale_le_exterior a d N β γ K hd (by omega) hL hK z hz
  have hscaled (cavity:Bool):
      truncatedMoment (RegularGraph.weight (N:=N) (d:=d))
        (momentSourceEvent N d a (exteriorWorkParameter cOriginal) β z)
        (fun g=>momentResidual cavity g (actualCavityDepth a d N z-1) z) p≤
          (Ctot*Real.log (N:ℝ)^(qtot:ℝ)*S)^(2*p):=by
    apply (hMoment z hz hzB hfloor cavity).trans
    apply pow_le_pow_left₀ (by have hh:=sourceHighMomentScale_nonnegative a d N β B z;positivity)
    apply (mul_le_mul_of_nonneg_left hcompare (by positivity:0≤C*Real.log (N:ℝ)^q)).trans_eq
    simp only [Real.rpow_natCast,Ctot,qtot,pow_add]
    ring
  have htail (cavity:Bool):eventMass (RegularGraph.weight (N:=N) (d:=d)) (fun g=>
      momentSourceEvent N d a (exteriorWorkParameter cOriginal) β z g ∧
        (N:ℝ)^e*S < ‖momentResidual cavity g (actualCavityDepth a d N z-1) z‖)≤1/(N:ℝ)^(D+1):=
    hMarkov RegularGraph.weight RegularGraph.weight_nonnegative _ _ S hS (hscaled cavity)
  have htailQ:=htail true
  have htailT:=htail false
  simp_rw [momentResidual_cavity_eq_physical] at htailQ
  simp_rw [momentResidual_trace_eq_physical] at htailT
  have hmass:eventMass (RegularGraph.weight (N:=N) (d:=d)) (fun g=>
      WorkTreeCountAux (exteriorAuxParameter cOriginal) (exteriorAuxCountExponent cOriginal) g ∧
        ExteriorWorkOmega a cOriginal β E g ∧¬ExteriorPhysicalResidualGood a β γ e 1 0 E g)≤
      eventMass (RegularGraph.weight (N:=N) (d:=d)) (fun g=>
        ExteriorWorkOmega a cOriginal β E g ∧(N:ℝ)^e*S < ‖physicalCavityFluctuation a g z‖)+
      eventMass (RegularGraph.weight (N:=N) (d:=d)) (fun g=>
        ExteriorWorkOmega a cOriginal β E g ∧(N:ℝ)^e*S < ‖physicalTraceFluctuation a g z‖):=by
    apply (eventMass_mono RegularGraph.weight RegularGraph.weight_nonnegative (Q:=fun g=>
      (ExteriorWorkOmega a cOriginal β E g ∧(N:ℝ)^e*S < ‖physicalCavityFluctuation a g z‖)∨
      (ExteriorWorkOmega a cOriginal β E g ∧(N:ℝ)^e*S < ‖physicalTraceFluctuation a g z‖)) ?_).trans
      (eventMass_union_le RegularGraph.weight RegularGraph.weight_nonnegative _ _)
    intro g hg
    have hbad:¬(‖physicalCavityFluctuation a g z‖≤(N:ℝ)^e*S ∧
        ‖physicalTraceFluctuation a g z‖≤(N:ℝ)^e*S):=by
      simpa only [ExteriorPhysicalResidualGood,pow_zero,mul_one,one_mul] using hg.2.2
    by_cases hQ:‖physicalCavityFluctuation a g z‖≤(N:ℝ)^e*S
    · exact Or.inr ⟨hg.2.1,lt_of_not_ge (fun hT=>hbad ⟨hQ,hT⟩)⟩
    · exact Or.inl ⟨hg.2.1,lt_of_not_ge hQ⟩
  apply hmass.trans
  apply (add_le_add htailQ htailT).trans
  have hNp:0<(N:ℝ):=Nat.cast_pos.mpr (by omega)
  calc
    _=2/((N:ℝ)^D*(N:ℝ)):=by rw [pow_succ];ring
    _≤1/(N:ℝ)^D:=by
      apply (div_le_iff₀ (by positivity:0<(N:ℝ)^D*(N:ℝ))).mpr
      have hc:(1/(N:ℝ)^D)*((N:ℝ)^D*(N:ℝ))=(N:ℝ):=by field_simp
      rw [hc]
      exact Nat.cast_le.mpr hN

end SpectralConsequences
