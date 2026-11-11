import SpectralConsequences.SourceRigidityAssembly

/-! Assembly of two all-polynomial conditional estimates with the original
structural denominator. This is an intermediate probability lemma. -/
open Filter
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance conditionalRigidityAssemblyDecidable (p:Prop):Decidable p:=Classical.propDecidable p

theorem conditional_rigidity_assembly (d:ℕ)(a b c β:ℝ)
    (hd:3≤d)(ha:12≤a)(hb:25*a≤b)(hc:0<c)(hc1:c<1)(hβ:0<β)(hβc:β≤c/32)
    (hconf:∀D:ℕ,∀ᶠ N:ℕ in atTop,Nonempty (RegularGraph N d)→
      eventMass (RegularGraph.weight (N:=N) (d:=d)) (fun g=>
        RegularGraph.structural (logarithmicRadius (c/4) d N) (finiteOmega d) ⌊(N:ℝ)^c⌋₊ g ∧
          ¬SourceConfinementGood β g)/
        eventMass (RegularGraph.weight (N:=N) (d:=d))
          (RegularGraph.structural (logarithmicRadius (c/4) d N) (finiteOmega d) ⌊(N:ℝ)^c⌋₊)≤1/(N:ℝ)^D):
    ∀D:ℕ,∀ᶠ N:ℕ in atTop,Nonempty (RegularGraph N d)→
      eventMass (RegularGraph.weight (N:=N) (d:=d)) (fun g=>
        RegularGraph.structural (logarithmicRadius (c/4) d N) (finiteOmega d) ⌊(N:ℝ)^c⌋₊ g ∧
          ¬SourceRigid hd (β/32) g)/
        eventMass (RegularGraph.weight (N:=N) (d:=d))
          (RegularGraph.structural (logarithmicRadius (c/4) d N) (finiteOmega d) ⌊(N:ℝ)^c⌋₊)≤1/(N:ℝ)^D:=by
  intro D
  filter_upwards [source_counting_rate d a b c β hd ha hb hc hc1 hβ hβc (D+1),
    hconf (D+1),eventually_source_rigid_of_counting_and_confinement d hd β hβ,
    eventually_ge_atTop 2] with N hcount hconf hrigid hN
  intro hnonempty
  let base:RegularGraph N d→Prop:=RegularGraph.structural
    (logarithmicRadius (c/4) d N) (finiteOmega d) ⌊(N:ℝ)^c⌋₊
  let w:=RegularGraph.weight (N:=N) (d:=d)
  have hden:0≤eventMass w base:=by
    unfold eventMass
    apply Finset.sum_nonneg
    intro g _
    split_ifs
    · exact RegularGraph.weight_nonnegative g
    · exact le_rfl
  have hmass:eventMass w (fun g=>base g ∧¬SourceRigid hd (β/32) g)≤
      eventMass w (fun g=>base g ∧¬SourceCountingCDFGood β g)+
      eventMass w (fun g=>base g ∧¬SourceConfinementGood β g):=by
    apply (eventMass_mono w RegularGraph.weight_nonnegative (Q:=fun g=>
      (base g ∧¬SourceCountingCDFGood β g)∨(base g ∧¬SourceConfinementGood β g)) ?_).trans
      (eventMass_union_le w RegularGraph.weight_nonnegative _ _)
    intro g hg
    by_cases hCDF:SourceCountingCDFGood β g
    · exact Or.inr ⟨hg.1,fun h=>hg.2 (hrigid g hCDF h)⟩
    · exact Or.inl ⟨hg.1,hCDF⟩
  apply (div_le_div_of_nonneg_right hmass hden).trans
  rw [add_div]
  apply (add_le_add (hcount hnonempty) (hconf hnonempty)).trans
  have hNp:0<(N:ℝ):=Nat.cast_pos.mpr (by omega)
  have hN2:(2:ℝ)≤N:=Nat.cast_le.mpr hN
  rw [pow_succ]
  apply (mul_le_mul_right (by positivity:(0:ℝ)<(N:ℝ)^D*(N:ℝ))).mp
  have hcancel:(1/(N:ℝ)^D)*((N:ℝ)^D*(N:ℝ))=(N:ℝ):=by field_simp
  have hid:(1/((N:ℝ)^D*(N:ℝ))+1/((N:ℝ)^D*(N:ℝ)))*((N:ℝ)^D*(N:ℝ))=2:=by field_simp; ring
  rw [hid,hcancel]
  exact hN2

end SpectralConsequences
