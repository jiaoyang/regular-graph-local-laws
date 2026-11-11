import SpectralConsequences.AllCoreReferenceLimit
import SpectralConsequences.AllCorePaperComplexity

/-! The corrected reference maximum over literal possibly infinite cores.
Complexity has finite deficit support and an actual finite feedback-edge set.
The diagonal bound is relative to |md| on all of C+, avoiding the printed
positive global constant lower bound, which PaperDefinitionSanity disproves.
-/
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1600000
namespace SpectralConsequences
open LocalLaw
local instance paperReferenceThresholdDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The all-core reference property with actual finite-feedback witnesses,
actual infinite tree-extension Green entries, and the necessary global
relative diagonal normalization. -/
def PaperReferenceThreshold (d ω : ℕ) (hd : 1≤d) : Prop :=
  ∃C:ℝ,1≤C ∧∀(V:Type)[DecidableEq V](g:AllCoreGraph V d),
    g.graph.Connected → g.PaperComplexity ω → ∀z:ℂ,0<z.im→
      (∀i j,‖g.green hd z i j‖≤C*‖-semicircleRoot z*treeEdgeWeight d‖^g.graph.dist i j) ∧
      (∀i j,|(g.green hd z i j).im|≤C*(kestenMcKayTransform d (semicircleRoot z) z).im) ∧
      (∀i,‖kestenMcKayTransform d (semicircleRoot z) z‖/C≤‖g.green hd z i i‖)

theorem paperReferenceThreshold_imp_finite (d ω : ℕ) (hd : 3≤d)
    (hclass : PaperReferenceThreshold d ω (by omega)) : FiniteReferenceThreshold d ω := by
  obtain ⟨C,hC,h⟩ := hclass
  refine ⟨C,hC,?_⟩
  intro V _ _ g hconn hbudget z hz
  have href := h V (AllCoreGraph.ofFinite g) hconn
    (AllCoreGraph.ofFinite_paperComplexity g hconn ω hbudget) z hz
  simpa only [AllCoreGraph.ofFinite_graph,AllCoreGraph.ofFinite_green g hd z hz,
    g.treeExtensionGreen_eq_extensionGreen hd z hz] using href

theorem finiteReferenceThreshold_imp_paper (d ω : ℕ) (hd : 3≤d)
    (hclass : FiniteReferenceThreshold d ω) : PaperReferenceThreshold d ω (by omega) := by
  obtain ⟨C,hC,h⟩ := finiteReferenceThreshold_imp_allCore d ω hd hclass
  refine ⟨C,hC,?_⟩
  intro V _ g hconn hbudget z hz
  exact h V g hconn hbudget.hereditary z hz

theorem paperReferenceThreshold_iff_finite (d ω : ℕ) (hd : 3≤d) :
    PaperReferenceThreshold d ω (by omega) ↔ FiniteReferenceThreshold d ω :=
  ⟨paperReferenceThreshold_imp_finite d ω hd,finiteReferenceThreshold_imp_paper d ω hd⟩

/-- A positive maximum exists over the actual possibly infinite-core class. -/
theorem exists_maximal_paperReferenceThreshold (d : ℕ) (hd : 3≤d) :
    ∃ω:ℕ,1≤ω ∧ PaperReferenceThreshold d ω (by omega) ∧
      ∀ω':ℕ,PaperReferenceThreshold d ω' (by omega)→ω'≤ω := by
  refine ⟨finiteOmega d,finiteOmega_positive d hd,
    finiteReferenceThreshold_imp_paper d (finiteOmega d) hd (finiteOmega_good d hd),?_⟩
  intro ω' hω'
  exact finiteOmega_maximal d hd ω' (paperReferenceThreshold_imp_finite d ω' hd hω')

/-- Defined as the genuine maximal integer in the corrected all-core class.
It is not defined as an alias for the finite maximum. -/
def paperOmega (d : ℕ) : ℕ :=
  if hd : 3≤d then Classical.choose (exists_maximal_paperReferenceThreshold d hd) else 0

theorem paperOmega_positive (d : ℕ) (hd : 3≤d) : 1≤paperOmega d := by
  unfold paperOmega
  rw [dif_pos hd]
  exact (Classical.choose_spec (exists_maximal_paperReferenceThreshold d hd)).1

theorem paperOmega_good (d : ℕ) (hd : 3≤d) :
    PaperReferenceThreshold d (paperOmega d) (by omega) := by
  unfold paperOmega
  rw [dif_pos hd]
  exact (Classical.choose_spec (exists_maximal_paperReferenceThreshold d hd)).2.1

theorem paperOmega_maximal (d ω : ℕ) (hd : 3≤d)
    (hω : PaperReferenceThreshold d ω (by omega)) : ω≤paperOmega d := by
  unfold paperOmega
  rw [dif_pos hd]
  exact (Classical.choose_spec (exists_maximal_paperReferenceThreshold d hd)).2.2 ω hω

/-- Equality follows from the proved equivalence of genuine all-core and
finite-core reference properties, rather than being a definition. -/
theorem paperOmega_eq_finiteOmega (d : ℕ) (hd : 3≤d) : paperOmega d=finiteOmega d := by
  apply Nat.le_antisymm
  · exact finiteOmega_maximal d hd (paperOmega d)
      (paperReferenceThreshold_imp_finite d (paperOmega d) hd (paperOmega_good d hd))
  · exact paperOmega_maximal d (finiteOmega d) hd
      (finiteReferenceThreshold_imp_paper d (finiteOmega d) hd (finiteOmega_good d hd))

end SpectralConsequences
#print axioms SpectralConsequences.paperReferenceThreshold_iff_finite
#print axioms SpectralConsequences.paperOmega_eq_finiteOmega
