import SpectralConsequences.SourceExteriorResidualBound
import SpectralConsequences.SourceExteriorConfinement
import SpectralConsequences.SourceWeakProbability
import SpectralConsequences.WorkTreeCountAuxiliary
import SpectralConsequences.ConditionalFiniteUnion

/-! # Original-conditioning confinement reduction from physical residual tails

This is an INTERMEDIATE probability reduction. Its only probabilistic input
is a stated tail bound for the two actual Section 7 residuals on the work weak
event and auxiliary event. No confinement or corrected-trace tail is assumed.
-/
open Filter Set
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1400000
namespace SpectralConsequences
open LocalLaw
local instance originalExteriorProbabilityDecidable (p:Prop):Decidable p:=Classical.propDecidable p

def exteriorAuxParameter (cOriginal:ℝ):ℝ:=min (cOriginal/2) (1/4)
def exteriorWorkParameter (cOriginal:ℝ):ℝ:=exteriorAuxParameter cOriginal/4
def exteriorAuxCountExponent (cOriginal:ℝ):ℝ:=7*exteriorAuxParameter cOriginal/32
def sourceExteriorProbabilityBound (d:ℕ):ℝ:=2*(d:ℝ)+sourceSpectralBox d+2

def exteriorSpectralPoint (β:ℝ) (N:ℕ) (E:ℝ):ℂ:=(E:ℂ)+(exteriorHeight β N:ℂ)*Complex.I

def ExteriorPhysicalResidualGood {N d:ℕ} (a:ℕ) (β γ e K:ℝ) (p:ℕ) (E:ℝ)
    (g:RegularGraph N d):Prop:=
  let z:=exteriorSpectralPoint β N E
  let threshold:=K*Real.log (N:ℝ)^p*(N:ℝ)^e*sourceExteriorFluctuationScale a d N β γ z
  ‖physicalCavityFluctuation a g z‖≤threshold ∧ ‖physicalTraceFluctuation a g z‖≤threshold

def ExteriorWorkOmega {N d:ℕ} (a:ℕ) (cOriginal β:ℝ) (E:ℝ) (g:RegularGraph N d):Prop:=
  g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
    (logarithmicRadius (exteriorWorkParameter cOriginal/4) d N) (finiteOmega d)
    ⌊(N:ℝ)^(exteriorWorkParameter cOriginal)⌋₊ (exteriorSpectralPoint β N E)

/-- The remaining actual fluctuation-averaging tail, deliberately separated
from the completed deterministic and probability reductions. -/
def ExteriorPhysicalResidualTails (a d:ℕ) (cOriginal β γ e K:ℝ) (p:ℕ):Prop:=
  ∀D:ℕ,∀ᶠ N:ℕ in atTop,∀E∈sourceExteriorMesh d N β,
    eventMass (RegularGraph.weight (N:=N) (d:=d)) (fun g=>
      WorkTreeCountAux (exteriorAuxParameter cOriginal) (exteriorAuxCountExponent cOriginal) g ∧
      ExteriorWorkOmega a cOriginal β E g ∧ ¬ExteriorPhysicalResidualGood a β γ e K p E g)≤1/(N:ℝ)^D

private theorem probability_bound_ge_box (d:ℕ):sourceSpectralBox d+2≤sourceExteriorProbabilityBound d:=by
  dsimp only[sourceExteriorProbabilityBound]
  have hh:0≤(d:ℝ):=Nat.cast_nonneg _
  linarith

private theorem probability_bound_ge_degree (d:ℕ):2*(d:ℝ)≤sourceExteriorProbabilityBound d:=by
  have hh:2≤sourceSpectralBox d:=le_max_left _ _
  dsimp only[sourceExteriorProbabilityBound]
  linarith

theorem eventually_source_residual_grid_implies_confinement (a b d:ℕ) (β γ e K:ℝ) (p:ℕ)
    (ha:0<a) (hd:3≤d) (hβ:0<β) (hβsmall:β≤1/128) (hγ:9/32≤γ)
    (he:0≤e) (heβ:e<β/16) (hK:1≤K):
    ∀ᶠ N:ℕ in atTop,∀g:RegularGraph N d,
      (∀E∈sourceExteriorMesh d N β,
        let z:=exteriorSpectralPoint β N E
        ‖g.Q z-semicircleRoot z‖≤scalarScale (spectralScale z)
          (graphPaperError a d N (logarithmicRadius β d N) z))→
      (∀E∈sourceExteriorMesh d N β,ExteriorPhysicalResidualGood a β γ e K p E g)→SourceConfinementGood β g:=by
  filter_upwards [eventually_exterior_source_parameters (a:ℝ) (b:ℝ) d β (sourceSpectralBox d) hd hβ hβsmall,
    eventually_source_exterior_corrected_trace a d β γ e (sourceExteriorProbabilityBound d) K p
      ha hd hβ hβsmall hγ he heβ hK] with N num htrace
  intro g hprior hres
  apply source_confinement_of_scaled_corrected_trace (a:ℝ) (b:ℝ) β g num
  intro E hE
  have hext:=exteriorMesh_energy_bounds (N^2) (sourceSpectralBox d) (edgeWindow β N) (exteriorHeight β N) E hE
  have hspec:=sourceExteriorMesh_spectral_bounds (a:ℝ) (b:ℝ) d N β num E hE
  have hB:=hspec.2.2.1.trans (probability_bound_ge_box d)
  simpa only[Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,
    Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_add] using
    htrace g E hext.2 hB (hprior E hE) (hres E hE).1 (hres E hE).2

private theorem original_aux_implies_work {N d:ℕ} (g:RegularGraph N d) (hd:3≤d)
    (cOriginal:ℝ) (hc:0<cOriginal) (hN:1≤N)
    (horig:RegularGraph.structural (logarithmicRadius (cOriginal/4) d N) (finiteOmega d) ⌊(N:ℝ)^cOriginal⌋₊ g)
    (haux:WorkTreeCountAux (exteriorAuxParameter cOriginal) (exteriorAuxCountExponent cOriginal) g):
    RegularGraph.structural (logarithmicRadius (exteriorWorkParameter cOriginal/4) d N) (finiteOmega d)
      ⌊(N:ℝ)^(exteriorWorkParameter cOriginal)⌋₊ g := by
  have hauxpos:0<exteriorAuxParameter cOriginal:=lt_min (by linarith) (by norm_num)
  have hauxle:exteriorAuxParameter cOriginal≤cOriginal/2:=min_le_left _ _
  have hworkle:exteriorWorkParameter cOriginal≤cOriginal:=by dsimp only[exteriorWorkParameter];linarith
  have hlog:0≤Real.log (N:ℝ):=Real.log_nonneg (by exact_mod_cast hN)
  have hk:0<Real.log ((d-1:ℕ):ℝ):=Real.log_pos (by exact_mod_cast (show 1<d-1 by omega))
  have hrad:logarithmicRadius (exteriorWorkParameter cOriginal/4) d N≤logarithmicRadius (cOriginal/4) d N:=by
    unfold logarithmicRadius
    apply Nat.floor_mono
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (show exteriorWorkParameter cOriginal/4≤cOriginal/4 by linarith only[hworkle]) hlog) hk.le
  have hcount:(nonTreeCenters g.graph (logarithmicRadius (exteriorWorkParameter cOriginal/4) d N)).card≤
      ⌊(N:ℝ)^(exteriorWorkParameter cOriginal)⌋₊:=by
    change (nonTreeCenters g.graph (logarithmicRadius (exteriorAuxParameter cOriginal/16) d N)).card≤_ at haux
    rw [show exteriorWorkParameter cOriginal/4=exteriorAuxParameter cOriginal/16 by unfold exteriorWorkParameter;ring]
    apply haux.trans
    apply Nat.floor_mono
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by dsimp only[exteriorAuxCountExponent,exteriorWorkParameter];linarith)
  exact ⟨fun v=>(graphBallExcess_mono_radius g.graph v hrad).trans (horig.1 v),hcount⟩

theorem source_confinement_original_of_residual_tails (a b d:ℕ) (cOriginal β γ e K:ℝ) (p:ℕ)
    (ha:12≤a) (hb:25*a≤b) (hd:3≤d) (hc:0<cOriginal) (hc1:cOriginal<1)
    (hβ:0<β) (hβwork:β≤exteriorWorkParameter cOriginal/32) (hβsmall:β≤1/128)
    (hγ:9/32≤γ) (he:0≤e) (heβ:e<β/16) (hK:1≤K)
    (htails:ExteriorPhysicalResidualTails a d cOriginal β γ e K p):
    ∀D:ℕ,∀ᶠ N:ℕ in atTop,Nonempty (RegularGraph N d)→
      eventMass (RegularGraph.weight (N:=N) (d:=d)) (fun g=>
        RegularGraph.structural (logarithmicRadius (cOriginal/4) d N) (finiteOmega d) ⌊(N:ℝ)^cOriginal⌋₊ g ∧
          ¬SourceConfinementGood β g)/
      eventMass (RegularGraph.weight (N:=N) (d:=d))
        (RegularGraph.structural (logarithmicRadius (cOriginal/4) d N) (finiteOmega d) ⌊(N:ℝ)^cOriginal⌋₊)≤1/(N:ℝ)^D:=by
  intro D
  let cAux:=exteriorAuxParameter cOriginal
  let cwork:=exteriorWorkParameter cOriginal
  let δ:=exteriorAuxCountExponent cOriginal
  let B:=sourceExteriorProbabilityBound d
  have hcAux:0<cAux:=lt_min (by linarith) (by norm_num)
  have hcAux1:cAux≤1/4:=min_le_right _ _
  have hcwork:0<cwork:=by dsimp only[cwork,exteriorWorkParameter];positivity
  have hcwork1:cwork<1:=by dsimp only[cwork,exteriorWorkParameter];linarith only[hcAux1]
  have hδ:3*cAux/16<δ:=by dsimp only[δ,exteriorAuxCountExponent];linarith only[hcAux]
  have hB:2*(d:ℝ)≤B:=probability_bound_ge_degree d
  filter_upwards [eventually_source_residual_grid_implies_confinement a b d β γ e K p (by omega) hd hβ hβsmall hγ he heβ hK,
    eventually_exterior_source_parameters (a:ℝ) (b:ℝ) d β (sourceSpectralBox d) hd hβ hβsmall,
    source_uniform_weak_failure a b d cwork β B ha hb hd hcwork hcwork1 hβ hβwork hB (D+1),
    eventually_workTreeCountAux_failure d (D+1) cAux δ hd hcAux.le hδ,
    htails (D+4),eventually_original_structural_mass_half d (finiteOmega d) cOriginal hd
      (finiteOmega_positive d hd) hc hc1,
    eventually_const_div_pow_succ_le 6 D,eventually_ge_atTop 3]
    with N hdet num hweak haux hpoint hmass habsorb hN
  intro hnonempty
  have hNp:0<(N:ℝ):=Nat.cast_pos.mpr (by omega)
  let w:=RegularGraph.weight (N:=N) (d:=d)
  let original:RegularGraph N d→Prop:=RegularGraph.structural (logarithmicRadius (cOriginal/4) d N)
    (finiteOmega d) ⌊(N:ℝ)^cOriginal⌋₊
  let aux:RegularGraph N d→Prop:=WorkTreeCountAux cAux δ
  let work:RegularGraph N d→Prop:=RegularGraph.structural (logarithmicRadius (cwork/4) d N)
    (finiteOmega d) ⌊(N:ℝ)^cwork⌋₊
  let weak:RegularGraph N d→Prop:=fun g=>∀z∈boundedLocalLawDomain N b B,
    (graphLocalLawFamilyWithRadii N d a (effectiveModelRadius a d N β) (logarithmicRadius β d N)).weak z g
  let point:ℝ→RegularGraph N d→Prop:=fun E g=>aux g ∧ ExteriorWorkOmega a cOriginal β E g ∧
    ¬ExteriorPhysicalResidualGood a β γ e K p E g
  have hdomain:∀E∈sourceExteriorMesh d N β,exteriorSpectralPoint β N E∈boundedLocalLawDomain N b B:=by
    intro E hE
    have hh:=sourceExteriorMesh_spectral_bounds (a:ℝ) (b:ℝ) d N β num E hE
    exact ⟨hh.2.2.1.trans (probability_bound_ge_box d),by simpa only[Real.rpow_natCast] using hh.2.1⟩
  have hcover:∀g:RegularGraph N d,(original g∧¬SourceConfinementGood β g)→
      (¬aux g)∨((work g∧¬weak g)∨∃E∈sourceExteriorMesh d N β,point E g):=by
    intro g hg
    by_cases ha:aux g
    · have hw:work g:=original_aux_implies_work g hd cOriginal hc (by omega) hg.1 ha
      by_cases hweakg:weak g
      · by_cases hall:∀E∈sourceExteriorMesh d N β,ExteriorPhysicalResidualGood a β γ e K p E g
        · exfalso
          apply hg.2
          apply hdet g _ hall
          intro E hE
          have ho:ExteriorWorkOmega a cOriginal β E g:=⟨hw,hweakg _ (hdomain E hE)⟩
          exact ho.2.1
        · right;right
          have hh:∃E∈sourceExteriorMesh d N β,¬ExteriorPhysicalResidualGood a β γ e K p E g:=by
            simpa only[not_forall,exists_prop] using hall
          obtain ⟨E,hE,hbad⟩:=hh
          exact ⟨E,hE,ha,⟨hw,hweakg _ (hdomain E hE)⟩,hbad⟩
      · exact Or.inr (Or.inl ⟨hw,hweakg⟩)
    · exact Or.inl ha
  have hpointmass:eventMass w (fun g=>∃E∈sourceExteriorMesh d N β,point E g)≤1/(N:ℝ)^(D+1):=by
    apply (eventMass_exists_finset_le _ w RegularGraph.weight_nonnegative point).trans
    calc
      _≤∑_E∈sourceExteriorMesh d N β,1/(N:ℝ)^(D+4):=Finset.sum_le_sum hpoint
      _=((sourceExteriorMesh d N β).card:ℝ)*(1/(N:ℝ)^(D+4)):=by simp
      _≤(N:ℝ)^3*(1/(N:ℝ)^(D+4)):=by gcongr;exact_mod_cast sourceExteriorMesh_card_le d N β hN
      _=1/(N:ℝ)^(D+1):=by rw [show D+4=(D+1)+3 by omega,pow_add];field_simp [ne_of_gt hNp];ring
  have hfail:eventMass w (fun g=>original g∧¬SourceConfinementGood β g)≤3/(N:ℝ)^(D+1):=by
    apply (eventMass_mono w RegularGraph.weight_nonnegative hcover).trans
    apply (eventMass_union_le w RegularGraph.weight_nonnegative _ _).trans
    have hinner: eventMass w (fun g=>(work g∧¬weak g)∨∃E∈sourceExteriorMesh d N β,point E g)≤
        2/(N:ℝ)^(D+1):=by
      apply (eventMass_union_le w RegularGraph.weight_nonnegative _ _).trans
      have hh:=add_le_add (hweak ⌊(N:ℝ)^cwork⌋₊) hpointmass
      exact hh.trans_eq (by ring)
    exact (add_le_add haux hinner).trans_eq (by ring)
  have hden:=hmass hnonempty
  have hcond:=conditional_budget_factor_two
    (eventMass w (fun g=>original g∧¬SourceConfinementGood β g)) (eventMass w original)
    (3/(N:ℝ)^(D+1)) (by positivity) hden hfail
  exact hcond.trans (by convert habsorb using 1;ring)

end SpectralConsequences
