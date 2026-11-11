import SpectralConsequences.SourceTheorem12
import SpectralConsequences.PaperConditionalTransfer
import LocalLaw.SourceReferenceIdentification

/-! # Theorem 1.2 with the paper's one-based ranks and original threshold

The original structural event may use any positive reference threshold
omega at most the proved finite-core maximum. In particular a threshold
satisfying the paper's reference bounds on actual finite-core infinite tree
extensions qualifies by the proved one-sided comparison. Equality of maxima
over all possibly infinite cores is neither assumed nor needed.
-/
open Filter MeasureTheory
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance paperTheorem12Decidable (p:Prop):Decidable p:=Classical.propDecidable p

/-- Literal one-based rank range 2 <= i <= N from article (1.2). -/
def PaperRigid {N d:ℕ} (hd:3 ≤ d) (α:ℝ) (g:RegularGraph N d):Prop:=
  ∀(i:ℕ)(hi:2 ≤ i)(hiN:i ≤ N),
    let j:Fin N:=⟨i-1,by omega⟩
    |sortedEigenvalues g.H_hermitian j-classicalLocation d hd j| ≤ (N:ℝ)^(-α)

theorem paperRigid_iff_sourceRigid {N d:ℕ} (hd:3 ≤ d) (α:ℝ) (g:RegularGraph N d):
    PaperRigid hd α g↔SourceRigid hd α g:=by
  constructor
  · intro h i hi
    have hh:=h (i.val+1) (by omega) (by omega)
    simpa only [Nat.add_sub_cancel,Fin.eta] using hh
  · intro h i hi hiN
    exact h ⟨i-1,by omega⟩ (by dsimp;omega)

/-- The classical location in the one-based formulation satisfies exactly
integral_gamma_i^2 rho_d = i/N, including gamma_N=-2. -/
theorem paper_classical_location_tail_integral (d:ℕ)(hd:3 ≤ d) {N:ℕ}
    (i:ℕ)(hi:2 ≤ i)(hiN:i ≤ N):
    let j:Fin N:=⟨i-1,by omega⟩
    (∫x in classicalLocation d hd j..2,LocalLaw.kestenMcKayDensity d x)=(i:ℝ)/(N:ℝ):=by
  have hh:=classicalLocation_tail_integral d hd (⟨i-1,by omega⟩:Fin N)
  have hcast:((i-1:ℕ):ℝ)+1=(i:ℝ):=by exact_mod_cast Nat.sub_add_cancel (by omega:1 ≤ i)
  simpa only [hcast] using hh

/-- Conditional rigidity on the original omega structural event, for every
real polynomial failure exponent. This uses the actual indexed Hermitian
spectrum and the actual Kesten--McKay density quantiles. -/
theorem paper_theorem_1_2 (d ω:ℕ)(c:ℝ)(hd:3 ≤ d)(hω:1 ≤ ω)
    (hωmax:ω ≤ finiteOmega d)(hc:0<c)(hc1:c<1):
    ∃α:ℝ,0<α ∧∀C:ℝ,∀ᶠ N:ℕ in atTop,Nonempty (RegularGraph N d) → 
      eventMass (RegularGraph.weight (N:=N) (d:=d)) (fun g=>
        RegularGraph.structural (logarithmicRadius (c/4) d N) ω ⌊(N:ℝ)^c⌋₊ g ∧
          ¬PaperRigid hd α g)/
        eventMass (RegularGraph.weight (N:=N) (d:=d))
          (RegularGraph.structural (logarithmicRadius (c/4) d N) ω ⌊(N:ℝ)^c⌋₊) ≤ 1/(N:ℝ)^C:=by
  refine ⟨canonicalRigidityExponent c,canonicalRigidityExponent_pos c hc,?_⟩
  apply source_conditional_transfer_real d ω c hd hω hωmax hc hc1
    (fun _ g=>PaperRigid hd (canonicalRigidityExponent c) g)
  intro D
  simpa only [paperRigid_iff_sourceRigid] using source_theorem_1_2 d c hd hc hc1 D

/-- An actual source finite-core reference class is enough to recover the
paper-conditioned conclusion; no identification of two maximal integers is
left as an assumption. -/
theorem paper_theorem_1_2_for_reference_threshold (d ω:ℕ)(c:ℝ)
    (hd:3 ≤ d)(hω:1 ≤ ω)(hc:0<c)(hc1:c<1)
    (href:SourceFiniteCoreReferenceThreshold d ω (by omega)):
    ∃α:ℝ,0<α ∧∀C:ℝ,∀ᶠ N:ℕ in atTop,Nonempty (RegularGraph N d) → 
      eventMass (RegularGraph.weight (N:=N) (d:=d)) (fun g=>
        RegularGraph.structural (logarithmicRadius (c/4) d N) ω ⌊(N:ℝ)^c⌋₊ g ∧
          ¬PaperRigid hd α g)/
        eventMass (RegularGraph.weight (N:=N) (d:=d))
          (RegularGraph.structural (logarithmicRadius (c/4) d N) ω ⌊(N:ℝ)^c⌋₊) ≤ 1/(N:ℝ)^C:=
  paper_theorem_1_2 d ω c hd hω (source_reference_threshold_le_finiteOmega d ω hd href) hc hc1

end SpectralConsequences
