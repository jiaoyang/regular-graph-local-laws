import LocalLaw.TreeExtensionResolvent
import LocalLaw.FiniteReferenceThreshold

/-! # Reference estimates for actual infinite tree extensions

The underlying core is finite, but the graph whose Green function occurs in
this class is the literal infinite tree extension and its bounded self-adjoint
operator on ell2. The proved compression identity identifies this class with
the finite reference class used by the local-law proof.

The diagonal lower estimate is relative to |md|, as required on an unbounded
spectral domain. This file does not identify the largest threshold over all
possibly infinite deficient cores. Restriction of any such larger reference
class to finite cores is enough for the one-sided threshold comparison below.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance treeExtensionClassDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Uniform reference estimates on actual infinite tree extensions of all
finite connected deficient cores. -/
def FiniteCoreTreeExtensionThreshold (d ω : ℕ) (hd : 1≤d) : Prop :=
  ∃ C : ℝ, 1≤C ∧ ∀ (V : Type) [Fintype V] [DecidableEq V] (g : DeficientGraph V d),
    g.graph.Connected → (∑v,g.deficit v)+graphExcess g.graph≤ω →
    ∀ z : ℂ, 0<z.im →
      (∀ i j, ‖g.treeExtensionGreen hd z i j‖≤
        C*‖-semicircleRoot z*treeEdgeWeight d‖^g.graph.dist i j) ∧
      (∀ i j, |(g.treeExtensionGreen hd z i j).im|≤
        C*(kestenMcKayTransform d (semicircleRoot z) z).im) ∧
      (∀ i, ‖kestenMcKayTransform d (semicircleRoot z) z‖/C≤
        ‖g.treeExtensionGreen hd z i i‖)

theorem finiteCoreTreeExtensionThreshold_iff (d ω : ℕ) (hd : 3≤d) :
    FiniteCoreTreeExtensionThreshold d ω (by omega) ↔ FiniteReferenceThreshold d ω := by
  constructor
  · rintro ⟨C,hC,h⟩
    refine ⟨C,hC,?_⟩
    intro V _ _ g hconn hbudget z hz
    have hg := h V g hconn hbudget z hz
    simpa only [g.treeExtensionGreen_eq_extensionGreen hd z hz] using hg
  · rintro ⟨C,hC,h⟩
    refine ⟨C,hC,?_⟩
    intro V _ _ g hconn hbudget z hz
    simpa only [g.treeExtensionGreen_eq_extensionGreen hd z hz] using h V g hconn hbudget z hz

/-- Every reference threshold valid even just on the actual finite-core tree
extensions is below the constructed finite maximum. In particular, restricting
an all-core reference class to this subfamily suffices; equality of maximal
classes is not needed for structural conditioning in the local law. -/
theorem treeExtension_threshold_le_finiteOmega (d ω : ℕ) (hd : 3≤d)
    (hω : FiniteCoreTreeExtensionThreshold d ω (by omega)) : ω≤finiteOmega d :=
  finiteOmega_maximal d hd ω ((finiteCoreTreeExtensionThreshold_iff d ω hd).mp hω)

/-- The finite maximum is attained by genuine infinite tree extensions. -/
theorem finiteOmega_treeExtension_good (d : ℕ) (hd : 3≤d) :
    FiniteCoreTreeExtensionThreshold d (finiteOmega d) (by omega) :=
  (finiteCoreTreeExtensionThreshold_iff d (finiteOmega d) hd).mpr (finiteOmega_good d hd)

namespace DeficientGraph
variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

/-- The three actual infinite-extension Green bounds at the finite maximum,
with precisely the same degree-dependent reference constant. -/
theorem finiteOmega_treeExtension_reference_bounds (g : DeficientGraph V d) (hd : 3≤d)
    (hconn : g.graph.Connected)
    (hbudget : (∑v,g.deficit v)+graphExcess g.graph≤finiteOmega d)
    (z : ℂ) (hz : 0<z.im) :
    (∀ i j, ‖g.treeExtensionGreen (by omega) z i j‖≤
      finiteReferenceConstant d*‖-semicircleRoot z*treeEdgeWeight d‖^g.graph.dist i j) ∧
    (∀ i j, |(g.treeExtensionGreen (by omega) z i j).im|≤
      finiteReferenceConstant d*(kestenMcKayTransform d (semicircleRoot z) z).im) ∧
    (∀ i, ‖kestenMcKayTransform d (semicircleRoot z) z‖/finiteReferenceConstant d≤
      ‖g.treeExtensionGreen (by omega) z i i‖) := by
  simpa only [g.treeExtensionGreen_eq_extensionGreen hd z hz] using
    finiteOmega_reference_bounds d hd g hconn hbudget z hz

end DeficientGraph
end LocalLaw
