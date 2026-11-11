import SpectralConsequences.SourceTheorem14Canonical
import SpectralConsequences.PaperConditionalTransfer

/-! The literal homogeneous sup-norm conclusion of article Theorem 1.4,
with the degree-dependent constant absorbed into the fixed power 151, and
with conditioning at any positive reference threshold below `finiteOmega`.
-/
open scoped BigOperators
open Matrix
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance paperTheorem14Decidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Every complex eigenvector, including unnormalized vectors and every vector
in a repeated eigenspace, satisfies the paper's homogeneous sup-norm bound.
The norm on the finite function space is the actual supremum norm. -/
def PaperDelocalized {N d : ℕ} (g : RegularGraph N d) : Prop :=
  ∀eig:ℝ,∀v:Fin N→ℂ,g.H *ᵥ v=(eig:ℂ) • v→
    ‖v‖≤Real.log (N:ℝ)^151/Real.sqrt (N:ℝ)*Real.sqrt (∑j,‖v j‖^2)

theorem sourceDelocalized_implies_paper {N d : ℕ} (g : RegularGraph N d)
    (hlog : 1≤Real.log (N:ℝ))
    (hC : sourceEigenvectorConstant d≤Real.log (N:ℝ))
    (hg : SourceDelocalized g) : PaperDelocalized g := by
  intro eig v heig
  have hNr : 0≤(N:ℝ) := Nat.cast_nonneg N
  have hS : 0≤∑j,‖v j‖^2 := Finset.sum_nonneg (fun _ _=>sq_nonneg _)
  have hlog0 : 0≤Real.log (N:ℝ) := by linarith
  have hC2 : sourceEigenvectorConstant d≤Real.log (N:ℝ)^2 := by
    have hh : Real.log (N:ℝ)≤Real.log (N:ℝ)^2 := by nlinarith
    exact hC.trans hh
  have hb : 0≤Real.log (N:ℝ)^151/Real.sqrt (N:ℝ)*Real.sqrt (∑j,‖v j‖^2) := by positivity
  have hsq : (Real.log (N:ℝ)^151/Real.sqrt (N:ℝ)*Real.sqrt (∑j,‖v j‖^2))^2=
      Real.log (N:ℝ)^302/(N:ℝ)*(∑j,‖v j‖^2) := by
    rw [mul_pow,div_pow,Real.sq_sqrt hNr,Real.sq_sqrt hS,←pow_mul]
  have hfactor : sourceEigenvectorConstant d*(Real.log (N:ℝ)^300/(N:ℝ))≤
      Real.log (N:ℝ)^302/(N:ℝ) := by
    calc
      _=(sourceEigenvectorConstant d*Real.log (N:ℝ)^300)/(N:ℝ) := by ring
      _≤(Real.log (N:ℝ)^2*Real.log (N:ℝ)^300)/(N:ℝ) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hC2 (pow_nonneg hlog0 _)) hNr
      _=Real.log (N:ℝ)^302/(N:ℝ) := by rw [←pow_add]
  apply (pi_norm_le_iff_of_nonneg hb).mpr
  intro i
  have hh := (hg eig v heig i).trans (mul_le_mul_of_nonneg_right hfactor hS)
  rw [←hsq] at hh
  nlinarith [norm_nonneg (v i)]

/-- Paper Theorem 1.4 at any positive structural threshold below the proved
finite reference maximum. No reference estimate or spectral event is assumed. -/
theorem paper_theorem_1_4 (d ω : ℕ) (c : ℝ)
    (hd : 3≤d) (hω : 1≤ω) (hωmax : ω≤finiteOmega d) (hc : 0<c) (hc1 : c<1) :
    ∀C:ℝ,∀ᶠ N:ℕ in Filter.atTop,Nonempty (RegularGraph N d)→
      eventMass (RegularGraph.weight (N:=N) (d:=d)) (fun g=>
        RegularGraph.structural (logarithmicRadius (c/4) d N) ω ⌊(N:ℝ)^c⌋₊ g∧¬PaperDelocalized g)/
      eventMass (RegularGraph.weight (N:=N) (d:=d))
        (RegularGraph.structural (logarithmicRadius (c/4) d N) ω ⌊(N:ℝ)^c⌋₊)≤1/(N:ℝ)^C := by
  apply source_conditional_transfer_real d ω c hd hω hωmax hc hc1
    (fun _ g=>PaperDelocalized g)
  intro D
  filter_upwards [source_theorem_1_4 d c hd hc hc1 D,
    eventually_log_ge_nat 1,eventually_log_ge_nat (sourceEigenvectorConstant d)] with N hprob hlog hC
  intro hnonempty
  have hnum : eventMass (RegularGraph.weight (N:=N) (d:=d)) (fun g=>
      RegularGraph.structural (logarithmicRadius (c/4) d N) (finiteOmega d) ⌊(N:ℝ)^c⌋₊ g∧¬PaperDelocalized g)≤
      eventMass (RegularGraph.weight (N:=N) (d:=d)) (fun g=>
      RegularGraph.structural (logarithmicRadius (c/4) d N) (finiteOmega d) ⌊(N:ℝ)^c⌋₊ g∧¬SourceDelocalized g) := by
    apply eventMass_mono RegularGraph.weight RegularGraph.weight_nonnegative
    intro g hg
    exact ⟨hg.1,fun h=>hg.2 (sourceDelocalized_implies_paper g hlog hC h)⟩
  have hden : 0≤eventMass (RegularGraph.weight (N:=N) (d:=d))
      (RegularGraph.structural (logarithmicRadius (c/4) d N) (finiteOmega d) ⌊(N:ℝ)^c⌋₊) := by
    unfold eventMass
    exact Finset.sum_nonneg (fun g _=>by split_ifs <;> first | exact RegularGraph.weight_nonnegative g | positivity)
  exact (div_le_div_of_nonneg_right hnum hden).trans (hprob hnonempty)

/-- The actual finite-core infinite-tree-extension class supplies precisely the
one-sided threshold comparison needed by the original conditioning event. -/
theorem paper_theorem_1_4_of_reference_threshold (d ω : ℕ) (c : ℝ)
    (hd : 3≤d) (hω : 1≤ω)
    (hreference : SourceFiniteCoreReferenceThreshold d ω (by omega))
    (hc : 0<c) (hc1 : c<1) :
    ∀C:ℝ,∀ᶠ N:ℕ in Filter.atTop,Nonempty (RegularGraph N d)→
      eventMass (RegularGraph.weight (N:=N) (d:=d)) (fun g=>
        RegularGraph.structural (logarithmicRadius (c/4) d N) ω ⌊(N:ℝ)^c⌋₊ g∧¬PaperDelocalized g)/
      eventMass (RegularGraph.weight (N:=N) (d:=d))
        (RegularGraph.structural (logarithmicRadius (c/4) d N) ω ⌊(N:ℝ)^c⌋₊)≤1/(N:ℝ)^C :=
  paper_theorem_1_4 d ω c hd hω
    (source_reference_threshold_le_finiteOmega d ω hd hreference) hc hc1

end SpectralConsequences
#print axioms SpectralConsequences.paper_theorem_1_4
#print axioms SpectralConsequences.paper_theorem_1_4_of_reference_threshold
