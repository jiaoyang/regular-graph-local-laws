import SpectralConsequences.AllCoreExhaustion
import SpectralConsequences.AllCoreFiniteSupportGreen
import SpectralConsequences.AllCorePaddedEmbedding

/-! Finite reference estimates imply reference estimates for every possibly
infinite core. Actual finite tree extensions converge strongly on ell2, and
the uniform estimates pass to their genuine resolvent entries. -/
open scoped BigOperators Topology
open Filter
noncomputable section
set_option maxHeartbeats 2400000
namespace SpectralConsequences
open LocalLaw
local instance allCoreLimitDecidable (p : Prop) : Decidable p := Classical.propDecidable p

namespace AllCoreGraph
variable {V : Type} [DecidableEq V] {d : ℕ}

omit [DecidableEq V] in
theorem finiteRestriction_dist_ge (g : AllCoreGraph V d) (S : Finset V)
    (hS : (g.finiteRestriction S).graph.Connected) (i j : S) :
    g.graph.dist i.val j.val≤(g.finiteRestriction S).graph.dist i j := by
  let f : (g.finiteRestriction S).graph →g g.graph :=
    { toFun := Subtype.val
      map_rel' := fun h => h }
  obtain ⟨p,hp⟩ := hS.exists_walk_length_eq_dist i j
  have hh := SimpleGraph.dist_le (p.map f)
  simpa only [SimpleGraph.Walk.length_map,hp] using hh

theorem finiteSupport_green_tendsto (g : AllCoreGraph V d) (hconn : g.graph.Connected)
    (root : V) (hd : 1≤d) (z : ℂ) (hz : 0<z.im) (i j : V) :
    Tendsto (fun n => (g.finiteSupport (allCoreBallFinset g.graph root n)).green hd z i j)
      atTop (𝓝 (g.green hd z i j)) := by
  let S := allCoreBallFinset g.graph root
  have hstar : ∀v,∀ᶠ n in atTop,v∈S n ∧ g.graph.neighborFinset v⊆S n := by
    intro v
    filter_upwards [allCoreBallFinset_eventually_star g.graph hconn root v] with n hn
    exact ⟨hn.1,fun w hw => hn.2 w ((SimpleGraph.mem_neighborFinset _ _ _).mp hw)⟩
  exact g.green_tendsto_of_core_agreement (fun n => g.finiteSupport (S n)) hd
    (g.finiteSupport_neighbors_eventually S hstar)
    (g.finiteSupport_deficit_eventually S
      (fun v => (hstar v).mono (fun _ h => h.1))) z hz i j

end AllCoreGraph

theorem finiteReferenceThreshold_imp_allCore (d ω : ℕ) (hd : 3≤d)
    (hclass : FiniteReferenceThreshold d ω) :
    AllCoreReferenceThreshold d ω (by omega) := by
  obtain ⟨C,hC,h⟩ := hclass
  refine ⟨C,hC,?_⟩
  intro V _ g hconn hbudget z hz
  obtain ⟨root⟩ := hconn.nonempty
  let S := allCoreBallFinset g.graph root
  have hS (n : ℕ) : (g.finiteRestriction (S n)).graph.Connected :=
    allCoreBallFinset_induce_connected g.graph root n
  have hlim (i j : V) := g.finiteSupport_green_tendsto hconn root (by omega) z hz i j
  have hmem (i : V) : ∀ᶠ n in atTop,i∈S n :=
    allCoreBallFinset_eventually_mem g.graph hconn root i
  have href (n : ℕ) := h (S n) (g.finiteRestriction (S n)) (hS n)
    (g.finiteRestriction_budget hbudget (S n) (hS n)) z hz
  have ht : ‖-semicircleRoot z*treeEdgeWeight d‖≤1 := by
    have hh := cycle_transfer_norm_le_three_quarters d hd (semicircleRoot z)
      (semicircleRoot_norm_le_one z)
    linarith
  refine ⟨?_,?_,?_⟩
  · intro i j
    apply le_of_tendsto (hlim i j).norm
    filter_upwards [hmem i,hmem j] with n hi hj
    let ii : S n := ⟨i,hi⟩
    let jj : S n := ⟨j,hj⟩
    have hb := (href n).1 ii jj
    rw [←(g.finiteRestriction (S n)).treeExtensionGreen_eq_extensionGreen hd z hz,
      ←g.finiteSupport_green_eq_finiteRestriction (S n) hd z hz ii jj] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one (norm_nonneg _) ht (g.finiteRestriction_dist_ge (S n) (hS n) ii jj))
      (by linarith : 0≤C))
  · intro i j
    have him := (Complex.continuous_im.tendsto (g.green (by omega) z i j)).comp (hlim i j)
    apply le_of_tendsto him.abs
    filter_upwards [hmem i,hmem j] with n hi hj
    let ii : S n := ⟨i,hi⟩
    let jj : S n := ⟨j,hj⟩
    have hb := (href n).2.1 ii jj
    rw [←(g.finiteRestriction (S n)).treeExtensionGreen_eq_extensionGreen hd z hz,
      ←g.finiteSupport_green_eq_finiteRestriction (S n) hd z hz ii jj] at hb
    exact hb
  · intro i
    apply ge_of_tendsto (hlim i i).norm
    filter_upwards [hmem i] with n hi
    let ii : S n := ⟨i,hi⟩
    have hb := (href n).2.2 ii
    rw [←(g.finiteRestriction (S n)).treeExtensionGreen_eq_extensionGreen hd z hz,
      ←g.finiteSupport_green_eq_finiteRestriction (S n) hd z hz ii ii] at hb
    exact hb

theorem allCoreReferenceThreshold_iff_finite (d ω : ℕ) (hd : 3≤d) :
    AllCoreReferenceThreshold d ω (by omega) ↔ FiniteReferenceThreshold d ω :=
  ⟨allCoreReferenceThreshold_imp_finite d ω hd,finiteReferenceThreshold_imp_allCore d ω hd⟩

theorem finiteOmega_allCore_reference (d : ℕ) (hd : 3≤d) :
    AllCoreReferenceThreshold d (finiteOmega d) (by omega) :=
  finiteReferenceThreshold_imp_allCore d (finiteOmega d) hd (finiteOmega_good d hd)

theorem finiteOmega_maximal_allCore (d : ℕ) (hd : 3≤d) :
    1≤finiteOmega d ∧ AllCoreReferenceThreshold d (finiteOmega d) (by omega) ∧
      ∀ω:ℕ,AllCoreReferenceThreshold d ω (by omega)→ω≤finiteOmega d :=
  ⟨finiteOmega_positive d hd,finiteOmega_allCore_reference d hd,
    fun ω h => allCoreReferenceThreshold_le_finiteOmega d ω hd h⟩

end SpectralConsequences
#print axioms SpectralConsequences.finiteReferenceThreshold_imp_allCore
#print axioms SpectralConsequences.finiteOmega_maximal_allCore
