import LocalLaw.KestenMcKayStieltjes
import LocalLaw.TreeExtensionReferenceClass

/-! # Identification of source reference objects

Both transforms below are the article's literal density Stieltjes integrals.
The Green function is that of the actual infinite tree extension on ell2.
Thus the finite matrices used in the local law implement the source objects,
with no assumed resolvent-compression or integral-identification equation.

As in the finite reference class, the diagonal lower bound is relative to
|md| on the unbounded upper half-plane. This corrects the printed global
comparable-to-one lower bound; bounded-region comparability follows separately.
No equivalence of maxima over arbitrary infinite deficient cores is asserted.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance sourceReferenceDecidable (p : Prop) : Decidable p := Classical.propDecidable p

namespace DeficientGraph
variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

/-- The actual infinite tree-extension Green function is the finite weighted
extension with weight equal to the semicircle density's Stieltjes transform. -/
theorem treeExtensionGreen_eq_source_extension (g : DeficientGraph V d) (hd : 3≤d)
    (z : ℂ) (hz : 0<z.im) (i j : V) :
    g.treeExtensionGreen (by omega) z i j=g.extensionGreen (semicircleStieltjes z) z i j := by
  rw [semicircleStieltjes_eq_root z hz]
  exact g.treeExtensionGreen_eq_extensionGreen hd z hz i j

end DeficientGraph

/-- The finite-core portion of the article's tree-extension reference class,
written entirely using actual infinite graph resolvents and density integrals.
Any all-core reference class restricts to this one. -/
def SourceFiniteCoreReferenceThreshold (d ω : ℕ) (hd : 1≤d) : Prop :=
  ∃ C : ℝ, 1≤C ∧ ∀ (V : Type) [Fintype V] [DecidableEq V] (g : DeficientGraph V d),
    g.graph.Connected → (∑v,g.deficit v)+graphExcess g.graph≤ω →
    ∀ z : ℂ, 0<z.im →
      (∀ i j, ‖g.treeExtensionGreen hd z i j‖≤
        C*‖-semicircleStieltjes z*treeEdgeWeight d‖^g.graph.dist i j) ∧
      (∀ i j, |(g.treeExtensionGreen hd z i j).im|≤C*(kestenMcKayStieltjes d z).im) ∧
      (∀ i, ‖kestenMcKayStieltjes d z‖/C≤‖g.treeExtensionGreen hd z i i‖)

theorem sourceFiniteCoreReferenceThreshold_iff (d ω : ℕ) (hd : 3≤d) :
    SourceFiniteCoreReferenceThreshold d ω (by omega) ↔ FiniteReferenceThreshold d ω := by
  rw [←finiteCoreTreeExtensionThreshold_iff d ω hd]
  constructor
  · rintro ⟨C,hC,h⟩
    refine ⟨C,hC,?_⟩
    intro V _ _ g hconn hbudget z hz
    simpa only [semicircleStieltjes_eq_root z hz,kestenMcKayStieltjes_eq_transform d hd z hz] using
      h V g hconn hbudget z hz
  · rintro ⟨C,hC,h⟩
    refine ⟨C,hC,?_⟩
    intro V _ _ g hconn hbudget z hz
    simpa only [semicircleStieltjes_eq_root z hz,kestenMcKayStieltjes_eq_transform d hd z hz] using
      h V g hconn hbudget z hz

/-- One-sided comparison is enough to place the original structural event in
the larger finite reference budget used by the generalized local law. -/
theorem source_reference_threshold_le_finiteOmega (d ω : ℕ) (hd : 3≤d)
    (hω : SourceFiniteCoreReferenceThreshold d ω (by omega)) : ω≤finiteOmega d :=
  finiteOmega_maximal d hd ω ((sourceFiniteCoreReferenceThreshold_iff d ω hd).mp hω)

theorem finiteOmega_source_reference_good (d : ℕ) (hd : 3≤d) :
    SourceFiniteCoreReferenceThreshold d (finiteOmega d) (by omega) :=
  (sourceFiniteCoreReferenceThreshold_iff d (finiteOmega d) hd).mpr (finiteOmega_good d hd)

end LocalLaw
