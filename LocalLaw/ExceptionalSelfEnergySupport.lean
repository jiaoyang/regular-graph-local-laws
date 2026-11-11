import LocalLaw.ExceptionalSelfEnergyMass
import LocalLaw.RestrictedReferenceModel

/-!
# Actual support and geometric decay at exceptional Schur ports

Only vertices incident to an actual exceptional boundary edge can support the
exceptional matrix. Containment of both radius-r balls forces every such port
to have distance at least r from both target vertices.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance exceptionalSupportDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type} [Fintype V] [DecidableEq V]

def exceptionalPorts (G : SimpleGraph V) (S : Set V) : Finset S :=
  Finset.univ.filter (fun u => ∃ a : (Sᶜ : Set V), ¬ordinaryCutVertex G S a ∧ G.Adj u.val a.val)

omit [DecidableEq V] in
theorem exceptionalCoupling_row_zero (G : SimpleGraph V) (d : ℕ) (S : Set V) (u : S)
    (hu : u ∉ exceptionalPorts G S) (a : (Sᶜ : Set V)) : exceptionalCutCoupling G d S u a = 0 := by
  have hnot : ¬(¬ordinaryCutVertex G S a ∧ G.Adj u.val a.val) := by
    intro h
    exact hu (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨a, h⟩⟩)
  simp only [exceptionalCutCoupling, if_neg hnot]

omit [DecidableEq V] in
theorem exceptionalCharge_zero_off_ports (G : SimpleGraph V) (d : ℕ) (S : Set V) (u : S)
    (hu : u ∉ exceptionalPorts G S) : exceptionalCutCharge G d S u = 0 := by
  apply Finset.sum_eq_zero
  intro a _
  have hnot : ¬(¬ordinaryCutVertex G S a ∧ G.Adj u.val a.val) := by
    intro h
    exact hu (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨a, h⟩⟩)
  exact if_neg hnot

omit [Fintype V] [DecidableEq V] in
theorem induced_distance_lower (G : SimpleGraph V) (S : Set V) (hS : (G.induce S).Connected) (a b : S) :
    G.dist a.val b.val ≤ (G.induce S).dist a b := by
  obtain ⟨p, hp⟩ := hS.exists_walk_length_eq_dist a b
  have hh := SimpleGraph.dist_le (p.map (SimpleGraph.Embedding.induce S).toHom)
  simpa only [SimpleGraph.Walk.length_map, hp] using hh

omit [DecidableEq V] in
theorem exceptional_port_distance (G : SimpleGraph V) (hG : G.Connected) (S : Set V)
    (i j : V) (r : ℕ) (hcontain : pairBallVertices G i j r ⊆ S)
    (u : S) (hu : u ∈ exceptionalPorts G S) : r ≤ G.dist i u.val ∧ r ≤ G.dist u.val j := by
  obtain ⟨a, _, hua⟩ := (Finset.mem_filter.mp hu).2
  have hfar : ∀ b : V, (G.edist b a.val ≤ (r : ℕ∞) → a.val ∈ S) → r ≤ G.dist b u.val := by
    intro b hb
    by_contra hr
    obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist b u.val
    let tail : G.Walk u.val a.val := SimpleGraph.Walk.cons hua SimpleGraph.Walk.nil
    have hlen : (p.append tail).length ≤ r := by
      simp only [SimpleGraph.Walk.length_append, tail, SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil, hp]
      omega
    exact a.property (hb ((SimpleGraph.edist_le (p.append tail)).trans (ENat.coe_le_coe.mpr hlen)))
  constructor
  · exact hfar i (fun h => hcontain (Or.inl h))
  · rw [show G.dist u.val j = G.dist j u.val from G.dist_comm]
    exact hfar j (fun h => hcontain (Or.inr h))

namespace DeficientGraph
variable {d : ℕ}

theorem exceptionalSelfEnergy_row_zero (g : DeficientGraph V d) (S : Set V) (q z : ℂ)
    (u v : S) (hu : u ∉ exceptionalPorts g.graph S) : g.exceptionalSelfEnergy S q z u v = 0 := by
  rw [exceptionalSelfEnergy, Matrix.sub_apply, g.unmatched_boundary_diagonal_eq S]
  have hp : (exceptionalCutCoupling g.graph d S * (g.delete S).extensionGreen q z *
      (exceptionalCutCoupling g.graph d S).transpose) u v = 0 := by
    simp only [Matrix.mul_apply, exceptionalCoupling_row_zero g.graph d S u hu, zero_mul,
      Finset.sum_const_zero]
  rw [hp]
  simp only [Matrix.smul_apply, Matrix.diagonal_apply, exceptionalCharge_zero_off_ports g.graph d S u hu,
    Complex.ofReal_zero, ite_self, smul_zero, sub_self]

theorem exceptionalSelfEnergy_column_zero (g : DeficientGraph V d) (S : Set V) (q z : ℂ)
    (u v : S) (hv : v ∉ exceptionalPorts g.graph S) : g.exceptionalSelfEnergy S q z u v = 0 := by
  rw [exceptionalSelfEnergy, Matrix.sub_apply, g.unmatched_boundary_diagonal_eq S]
  have hp : (exceptionalCutCoupling g.graph d S * (g.delete S).extensionGreen q z *
      (exceptionalCutCoupling g.graph d S).transpose) u v = 0 := by
    rw [Matrix.mul_apply]
    simp only [Matrix.transpose_apply, exceptionalCoupling_row_zero g.graph d S v hv,
      mul_zero, Finset.sum_const_zero]
  rw [hp]
  by_cases huv : u = v
  · subst v
    simp only [Matrix.smul_apply, Matrix.diagonal_apply_eq,
      exceptionalCharge_zero_off_ports g.graph d S u hv, Complex.ofReal_zero, smul_zero, sub_self]
  · simp only [Matrix.smul_apply, Matrix.diagonal_apply_ne _ huv, smul_zero, sub_self]

theorem exceptionalSelfEnergy_support (g : DeficientGraph V d) (S : Set V) (q z : ℂ) (u v : S)
    (h : g.exceptionalSelfEnergy S q z u v ≠ 0) :
    u ∈ exceptionalPorts g.graph S ∧ v ∈ exceptionalPorts g.graph S := by
  constructor
  · by_contra hu
    exact h (g.exceptionalSelfEnergy_row_zero S q z u v hu)
  · by_contra hv
    exact h (g.exceptionalSelfEnergy_column_zero S q z u v hv)

end DeficientGraph
end LocalLaw
