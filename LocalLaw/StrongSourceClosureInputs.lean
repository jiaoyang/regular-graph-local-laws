import LocalLaw.StrongCertificateClosure
import LocalLaw.IndependentRadiusSourceCaps
import LocalLaw.PolynomialDensityAbsorption

/-!
# Actual strong closure budgets and exceptional-center absorption

All spectral, selected-depth, fourth-power averaging and quadratic-log row
budgets are realized uniformly in the bounded source domain. The stronger
sparse auxiliary event supplies the exceptional contribution.
-/

noncomputable section
namespace LocalLaw
local instance strongSourceClosureInputsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem eventually_strong_source_closure_inputs (a b d : ℕ) (c β γ B U V M0 : ℝ)
    (ha : 12≤a) (hb : 25*a≤b) (hd : 3≤d) (hc : 0<c)
    (hβ : 0<β) (hβc : β≤c/32) (hγβ : γ+β<1)
    (hB : 0≤B) (hU : 0≤U) (hV : 0≤V) (hM0 : 0<M0) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ z : ℂ,0<z.im → ‖z‖≤B → Real.log (N:ℝ)^b/(N:ℝ)≤z.im →
      ∃ D : StrongClosureBudget z (semicircleRoot z) (spectralScale z) (graphPaperError a d N (logarithmicRadius β d N) z),
        D.depth=actualCavityDepth a d N z ∧ D.L=Real.log (N:ℝ) ∧ D.U=U ∧ D.V=V ∧ D.residualConstant=M0 ∧
        D.rowBase=U*graphPaperError a d N (logarithmicRadius β d N) z/Real.log (N:ℝ) ∧
        D.rowFeedback=V*Real.log (N:ℝ)^2 ∧
        D.cavityError=M0*graphPaperError a d N (logarithmicRadius β d N) z/(2*Real.log (N:ℝ)^4) ∧
        D.exceptionalCavity=sourceExceptionalCavityCap d B ∧
        ∀ g : RegularGraph N d,
          RegularGraph.offsetStructural (logarithmicRadius (c/4) d N) (finiteOmega d) 1 ⌊(N:ℝ)^γ⌋₊ g →
          (graphLocalLawFamilyWithRadii N d a (effectiveModelRadius a d N β) (logarithmicRadius β d N)).weak z g →
          (∀ i∈nonTreeCenters g.graph (logarithmicRadius (c/4) d N),
            ‖cavityAtVertex g.graph d z i-cavityIterate z (g.Q z) D.depth‖≤D.exceptionalCavity) ∧
          D.cavityError+(((nonTreeCenters g.graph (logarithmicRadius (c/4) d N)).card:ℝ)/(N:ℝ))*D.exceptionalCavity≤
            D.residualConstant*graphPaperError a d N (logarithmicRadius β d N) z/D.L^4 := by
  let M := sourceExceptionalCavityCap d B
  let G := Real.sqrt (B+2)
  let C := strongLocalNormConstant B G M0
  let F := strongLocalFeedbackConstant B G M0
  have hM : 0≤M := sourceExceptionalCavityCap_nonnegative d hd B hB
  filter_upwards [eventually_actual_cavity_parameters a b d β ha hb hd hβ,
    eventually_log_ge_nat 2,eventually_log_ge_nat (2*C),eventually_log_ge_nat (2*(U+V*F)),
    RegularGraph.eventually_sourceOmegaWithRadii_exceptional_cavity_cap a b d c β B ha hb hd hc hβ hβc hB,
    eventually_polynomial_density_absorbed a d 4 β γ (2*M/M0) hd hβ.le hγβ,
    Filter.eventually_ge_atTop 1] with N hparameters hlog hscalar hrow hcaps hdensity hN
  intro z hz hzB hfloor
  let ε := graphPaperError a d N (logarithmicRadius β d N) z
  let L := Real.log (N:ℝ)
  have hLp : 0<L := by dsimp only [L]; linarith
  have hp := hparameters z hz hfloor
  have hε : 0<ε := inflateError_positive hLp (baseError_positive L a d N _ z.im _ hLp (by omega) (by omega) hz)
  let D := StrongClosureBudget.ofSemicircle z ε (actualCavityDepth a d N z) L B U V M0
    (U*ε/L) (V*L^2) (M0*ε/(2*L^4)) M hz hzB hp.2.2.2 hp.2.2.1 hε hU hV hM0.le hlog
    (paperError_dichotomy a d N _ z _ hLp) (by positivity) le_rfl le_rfl hscalar hrow
  refine ⟨D,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
  intro g haux hweak
  have hstruct := RegularGraph.offsetStructural_implies_structural haux
  have hOmega : g.SourceOmegaWithRadii a (effectiveModelRadius a d N β) (logarithmicRadius β d N)
      (logarithmicRadius (c/4) d N) (finiteOmega d) ⌊(N:ℝ)^γ⌋₊ z := ⟨hstruct,hweak⟩
  have hbad : ((nonTreeCenters g.graph (logarithmicRadius (c/4) d N)).card:ℝ)≤(N:ℝ)^γ :=
    (Nat.cast_le.mpr hstruct.2).trans (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) γ))
  constructor
  · intro i _
    exact hcaps g z _ hz hzB hfloor hOmega i
  · have hnum := hdensity z hz.le
    have hh := mul_le_mul_of_nonneg_left hnum (show 0≤M0/2 by positivity)
    have hfactor : M0/2*(2*M/M0)=M := by field_simp [ne_of_gt hM0]; ring
    have htail : M*(N:ℝ)^γ/(N:ℝ)≤M0*ε/(2*L^4) := by
      calc
        _ = (M0/2)*((2*M/M0)*(N:ℝ)^γ/(N:ℝ)) := by
          rw [←mul_div_assoc,←mul_assoc,hfactor]
        _ ≤ (M0/2)*(ε/L^4) := hh
        _ = _ := by ring
    have hbadTerm : (((nonTreeCenters g.graph (logarithmicRadius (c/4) d N)).card:ℝ)/(N:ℝ))*M≤M0*ε/(2*L^4) := by
      apply (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hbad (Nat.cast_nonneg N)) hM).trans
      convert htail using 1; ring
    change M0*ε/(2*L^4)+_≤M0*ε/L^4
    exact (add_le_add_left hbadTerm _).trans_eq (by ring)

end LocalLaw
