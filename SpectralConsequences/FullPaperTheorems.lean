import SpectralConsequences.PaperReferenceThreshold
import SpectralConsequences.PaperEvent
import SpectralConsequences.PaperTheorem12
import SpectralConsequences.PaperAllEigenvectors

/-! Canonical paper-form spectral conclusions: the genuine maximal corrected
all-core threshold, the literal real-radius structural event, and the actual
uniform law on that event. The positive conditioning denominator is proved.
No reference, resampling, moment, or spectral certificate is a hypothesis.
-/
open Filter
noncomputable section
set_option maxHeartbeats 1600000
namespace SpectralConsequences
open LocalLaw
local instance fullPaperTheoremsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The literal structural subtype on which the paper places uniform measure. -/
abbrev PaperGraph (N d : ℕ) (c : ℝ) :=
  {g:RegularGraph N d // PaperStructural c (paperOmega d) g}

private theorem positive_eventMass_implies_nonempty {X:Type*}[Fintype X]
    (w:X→ℝ)(A:X→Prop)(hpos:0<eventMass w A) : Nonempty {x:X//A x} := by
  by_contra hnot
  have hA : ∀x,¬A x := fun x hx=>hnot ⟨⟨x,hx⟩⟩
  have hzero : eventMass w A=0 := by
    unfold eventMass
    exact Finset.sum_eq_zero (fun x _=>if_neg (hA x))
  rw [hzero] at hpos
  exact (lt_irrefl 0) hpos

/-- The original structural subtype is eventually nonempty on every
admissible regular-graph ensemble; conditioning is not a totalized zero ratio. -/
theorem eventually_paper_structural_nonempty (d ω:ℕ)(c:ℝ)
    (hd:3≤d)(hω:1≤ω)(hc:0<c)(hc1:c<1) :
    ∀ᶠ N:ℕ in atTop,Nonempty (RegularGraph N d)→
      Nonempty {g:RegularGraph N d // PaperStructural c ω g} := by
  filter_upwards [eventually_original_structural_mass_half d ω c hd hω hc hc1,
    Filter.eventually_ge_atTop 1] with N hmass hN
  intro hnonempty
  apply positive_eventMass_implies_nonempty (RegularGraph.weight (N:=N) (d:=d))
  have hpred : PaperStructural c ω =
      RegularGraph.structural (logarithmicRadius (c/4) d N) ω ⌊(N:ℝ)^c⌋₊ :=
    funext (fun g=>propext (paperStructural_iff c ω g hd hN hc.le))
  rw [hpred]
  have hh := hmass hnonempty
  linarith

/-- The existing floor-radius conditional expression is exactly the paper's
uniform-on-structural-subtype probability, not only an asymptotic comparison. -/
theorem paper_conditional_failure_eq_uniform {N d:ℕ}(c:ℝ)(ω:ℕ)
    (hd:3≤d)(hN:1≤N)(hc:0≤c)(failure:RegularGraph N d→Prop)
    (hbar:Nonempty {g:RegularGraph N d // PaperStructural c ω g}) :
    eventMass (RegularGraph.weight (N:=N) (d:=d)) (fun g=>
      RegularGraph.structural (logarithmicRadius (c/4) d N) ω ⌊(N:ℝ)^c⌋₊ g∧failure g)/
      eventMass (RegularGraph.weight (N:=N) (d:=d))
        (RegularGraph.structural (logarithmicRadius (c/4) d N) ω ⌊(N:ℝ)^c⌋₊)=
      eventMass (finiteUniformWeight {g:RegularGraph N d // PaperStructural c ω g})
        (fun g=>failure g.val) := by
  letI := hbar
  have hh := conditional_uniform_eq_subtype_uniform (PaperStructural c ω) failure
  change eventMass (RegularGraph.weight (N:=N) (d:=d)) (fun g=>PaperStructural c ω g∧failure g)/
    eventMass (RegularGraph.weight (N:=N) (d:=d)) (PaperStructural c ω)=_ at hh
  have hpred : PaperStructural c ω =
      RegularGraph.structural (logarithmicRadius (c/4) d N) ω ⌊(N:ℝ)^c⌋₊ :=
    funext (fun g=>propext (paperStructural_iff c ω g hd hN hc))
  have hboth : (fun g:RegularGraph N d=>PaperStructural c ω g∧failure g)=
      (fun g=>RegularGraph.structural (logarithmicRadius (c/4) d N) ω ⌊(N:ℝ)^c⌋₊ g∧failure g) := by
    rw [hpred]
  have hnum := congrArg (eventMass (RegularGraph.weight (N:=N) (d:=d))) hboth
  have hden := congrArg (eventMass (RegularGraph.weight (N:=N) (d:=d))) hpred
  rw [hnum,hden] at hh
  exact hh

/-- Article Theorem 1.2 in its actual one-based rank range and actual uniform
measure on the original real-radius structural event, at the proved all-core
maximum. Multiplicities are retained and only the distinguished first mode is
excluded. The weak power rate is positive; no sharp edge scale is asserted. -/
theorem full_paper_theorem_1_2 (d:ℕ)(c:ℝ)(hd:3≤d)(hc:0<c)(hc1:c<1) :
    ∃α:ℝ,0<α ∧∀C:ℝ,∀ᶠ N:ℕ in atTop,Nonempty (RegularGraph N d)→
      Nonempty (PaperGraph N d c) ∧
      eventMass (finiteUniformWeight (PaperGraph N d c))
        (fun g=>¬PaperRigid hd α g.val)≤1/(N:ℝ)^C := by
  obtain ⟨α,hα,hprob⟩ := paper_theorem_1_2 d (paperOmega d) c hd
    (paperOmega_positive d hd) (by rw [paperOmega_eq_finiteOmega d hd]) hc hc1
  refine ⟨α,hα,?_⟩
  intro C
  filter_upwards [hprob C,eventually_paper_structural_nonempty d (paperOmega d) c hd
    (paperOmega_positive d hd) hc hc1,Filter.eventually_ge_atTop 1] with N hprob hbar hN
  intro hnonempty
  have hb := hbar hnonempty
  refine ⟨hb,?_⟩
  rw [←paper_conditional_failure_eq_uniform c (paperOmega d) hd hN hc.le
    (fun g=>¬PaperRigid hd α g) hb]
  exact hprob hnonempty

/-- Article Theorem 1.4 with coefficient-free fixed logarithmic power 151,
all vectors in every eigenspace, and the genuine conditional uniform law. -/
theorem full_paper_theorem_1_4 (d:ℕ)(c:ℝ)(hd:3≤d)(hc:0<c)(hc1:c<1) :
    ∀C:ℝ,∀ᶠ N:ℕ in atTop,Nonempty (RegularGraph N d)→
      Nonempty (PaperGraph N d c) ∧
      eventMass (finiteUniformWeight (PaperGraph N d c))
        (fun g=>¬PaperAllEigenvectors g.val)≤1/(N:ℝ)^C := by
  intro C
  filter_upwards [paper_theorem_1_4_all_eigenvectors d (paperOmega d) c hd
      (paperOmega_positive d hd) (by rw [paperOmega_eq_finiteOmega d hd]) hc hc1 C,
    eventually_paper_structural_nonempty d (paperOmega d) c hd
      (paperOmega_positive d hd) hc hc1,Filter.eventually_ge_atTop 1] with N hprob hbar hN
  intro hnonempty
  have hb := hbar hnonempty
  refine ⟨hb,?_⟩
  rw [←paper_conditional_failure_eq_uniform c (paperOmega d) hd hN hc.le
    (fun g=>¬PaperAllEigenvectors g) hb]
  exact hprob hnonempty

/-- Theorem 1.2 expressed as the ratio under the original uniform ensemble,
with precisely the same literal real-radius structural event. -/
theorem full_paper_theorem_1_2_ratio (d:ℕ)(c:ℝ)(hd:3≤d)(hc:0<c)(hc1:c<1) :
    ∃α:ℝ,0<α ∧∀C:ℝ,∀ᶠ N:ℕ in atTop,Nonempty (RegularGraph N d)→
      eventMass (RegularGraph.weight (N:=N) (d:=d)) (fun g=>
        PaperStructural c (paperOmega d) g∧¬PaperRigid hd α g)/
      eventMass (RegularGraph.weight (N:=N) (d:=d)) (PaperStructural c (paperOmega d))≤1/(N:ℝ)^C := by
  obtain ⟨α,hα,hprob⟩ := full_paper_theorem_1_2 d c hd hc hc1
  refine ⟨α,hα,?_⟩
  intro C
  filter_upwards [hprob C] with N hprob
  intro hnonempty
  have hh := hprob hnonempty
  letI : Nonempty (PaperGraph N d c) := hh.1
  change eventMass (finiteUniformWeight (RegularGraph N d))
    (fun g=>PaperStructural c (paperOmega d) g∧¬PaperRigid hd α g)/
    eventMass (finiteUniformWeight (RegularGraph N d)) (PaperStructural c (paperOmega d))≤_
  rw [conditional_uniform_eq_subtype_uniform]
  exact hh.2

/-- The homogeneous all-vector Theorem 1.4 in original-ensemble ratio form. -/
theorem full_paper_theorem_1_4_ratio (d:ℕ)(c:ℝ)(hd:3≤d)(hc:0<c)(hc1:c<1) :
    ∀C:ℝ,∀ᶠ N:ℕ in atTop,Nonempty (RegularGraph N d)→
      eventMass (RegularGraph.weight (N:=N) (d:=d)) (fun g=>
        PaperStructural c (paperOmega d) g∧¬PaperAllEigenvectors g)/
      eventMass (RegularGraph.weight (N:=N) (d:=d)) (PaperStructural c (paperOmega d))≤1/(N:ℝ)^C := by
  intro C
  filter_upwards [full_paper_theorem_1_4 d c hd hc hc1 C] with N hprob
  intro hnonempty
  have hh := hprob hnonempty
  letI : Nonempty (PaperGraph N d c) := hh.1
  change eventMass (finiteUniformWeight (RegularGraph N d))
    (fun g=>PaperStructural c (paperOmega d) g∧¬PaperAllEigenvectors g)/
    eventMass (finiteUniformWeight (RegularGraph N d)) (PaperStructural c (paperOmega d))≤_
  rw [conditional_uniform_eq_subtype_uniform]
  exact hh.2

end SpectralConsequences
#print axioms SpectralConsequences.full_paper_theorem_1_2
#print axioms SpectralConsequences.full_paper_theorem_1_4

#print axioms SpectralConsequences.full_paper_theorem_1_2_ratio
#print axioms SpectralConsequences.full_paper_theorem_1_4_ratio
