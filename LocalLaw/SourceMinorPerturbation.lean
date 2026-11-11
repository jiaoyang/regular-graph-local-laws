import LocalLaw.SourceEndpointPerturbation
import LocalLaw.PhysicalMinorSurgery

/-!
# Deleting an accepted sampled b removes its own outside switching

The old and new outside edges of one switching both meet its sampled first
endpoint b. After deleting b, only the other selected exterior triples can
support a perturbation. This is proved for the actual labelled schedule.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance sourceMinorPerturbationDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*}

theorem applySwitches_adj_of_no_footprints (L : List (SwitchingQuad V)) (G : SimpleGraph V)
    (x y : V) (h : ∀ q ∈ L, ¬q.footprint.Adj x y) :
    (applySwitches L G).Adj x y ↔ G.Adj x y := by
  induction L generalizing G with
  | nil => rfl
  | cons q L ih =>
    rw [applySwitches_cons]
    exact (ih (q.apply G) (fun p hp => h p (by simp [hp]))).trans
      (q.adj_outside_footprint G (h q (by simp)))

theorem SwitchingQuad.no_footprint_after_removing_roots (q : SwitchingQuad V) (x y : V)
    (hxa : x ≠ q.a) (hya : y ≠ q.a) (hxc : x ≠ q.c) (hyc : y ≠ q.c) : ¬q.footprint.Adj x y := by
  simp only [SwitchingQuad.footprint, switchingRemoved, switchingAdded, SimpleGraph.sup_adj,
    SimpleGraph.edge_adj]
  aesop

namespace LabelledResamplingState
variable {T : Set V} {ι : Type*} [Fintype ι]

def sampledOutsideFirst (s : LabelledResamplingState V T ι) (i : ι) : (Tᶜ : Set V) :=
  sampledFirstOutsideVertex s.graph T s.samples (s.boundary i)

def otherOutsideEndpoints (s : LabelledResamplingState V T ι) (selector : ℕ) (i : ι) :
    Set {v : (Tᶜ : Set V) // v ≠ s.sampledOutsideFirst i} :=
  {x | ∃ j, s.Eligible selector j ∧ j ≠ i ∧ x.val.val ∈ (s.quad j).exterior}

theorem fullResample_minor_adj_of_away_left (s : LabelledResamplingState V T ι)
    (selector : ℕ) (i : ι)
    (x y : {v : (Tᶜ : Set V) // v ≠ s.sampledOutsideFirst i})
    (hx : x ∉ s.otherOutsideEndpoints selector i) :
    (s.fullResample selector).graph.Adj x.val.val y.val.val ↔ s.graph.Adj x.val.val y.val.val := by
  rw [s.fullResample_graph_eq_applySwitches selector]
  apply applySwitches_adj_of_no_footprints
  intro q hq
  obtain ⟨j, _, hj, hqj⟩ := (s.mem_selectedQuads selector _ q).mp hq
  subst q
  have hroot : (s.quad j).a ∈ T := sampledSwitching_root_mem s.graph T s.samples (s.boundary j)
  have hxa : x.val.val ≠ (s.quad j).a := fun h => x.val.property (h ▸ hroot)
  have hya : y.val.val ≠ (s.quad j).a := fun h => y.val.property (h ▸ hroot)
  by_cases hji : j = i
  · subst j
    apply (s.quad i).no_footprint_after_removing_roots _ _ hxa hya
    · intro h
      exact x.property (Subtype.ext h)
    · intro h
      exact y.property (Subtype.ext h)
  · intro hfoot
    have hs := (s.quad j).footprint_left_mem_support hfoot
    change x.val.val = (s.quad j).a ∨ x.val.val ∈ (s.quad j).exterior at hs
    exact (hs.resolve_left hxa) |> fun he => hx ⟨j, hj, hji, he⟩

variable [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem fullResample_minor_difference_supported (s : LabelledResamplingState V T ι)
    (selector d : ℕ) (i : ι)
    (x y : {v : (Tᶜ : Set V) // v ≠ s.sampledOutsideFirst i})
    (haway : x ∉ s.otherOutsideEndpoints selector i ∨ y ∉ s.otherOutsideEndpoints selector i) :
    (deletedMatrix (normalizedAdjacency (outsideGraph (s.fullResample selector).graph T) d) (s.sampledOutsideFirst i) -
      deletedMatrix (normalizedAdjacency (outsideGraph s.graph T) d) (s.sampledOutsideFirst i)) x y = 0 := by
  have hagree : (s.fullResample selector).graph.Adj x.val.val y.val.val ↔ s.graph.Adj x.val.val y.val.val := by
    rcases haway with hx | hy
    · exact s.fullResample_minor_adj_of_away_left selector i x y hx
    · rw [(s.fullResample selector).graph.adj_comm, s.graph.adj_comm]
      exact s.fullResample_minor_adj_of_away_left selector i y x hy
  change (outsideGraph (s.fullResample selector).graph T).Adj x.val y.val ↔
    (outsideGraph s.graph T).Adj x.val y.val at hagree
  simp only [deletedMatrix, Matrix.submatrix_apply, Matrix.sub_apply, normalizedAdjacency,
    Matrix.smul_apply, smul_eq_mul, SimpleGraph.adjMatrix_apply]
  rw [hagree, sub_self]

theorem fullResample_minor_endpoint_mass {I : Type*} [Fintype I]
    (s : LabelledResamplingState V T ι) (selector d : ℕ) (i : ι)
    (hdegree : ∀ v, s.graph.degree v ≤ d)
    (e : I ↪ {v : (Tᶜ : Set V) // v ≠ s.sampledOutsideFirst i}) :
    let W := (deletedMatrix (normalizedAdjacency (outsideGraph (s.fullResample selector).graph T) d) (s.sampledOutsideFirst i) -
      deletedMatrix (normalizedAdjacency (outsideGraph s.graph T) d) (s.sampledOutsideFirst i)).submatrix e e
    (∀ u, ∑ v, ‖W u v‖ ≤ 2 * (d : ℝ) / Real.sqrt ((d : ℝ) - 1)) ∧
      (∀ v, ∑ u, ‖W u v‖ ≤ 2 * (d : ℝ) / Real.sqrt ((d : ℝ) - 1)) := by
  let f : I ↪ (Tᶜ : Set V) := ⟨fun u => (e u).val, fun _ _ h => e.injective (Subtype.ext h)⟩
  exact s.fullResample_outside_endpoint_mass selector d hdegree f

theorem fullResample_minor_endpoint_updates {I : Type*} [Fintype I]
    (s : LabelledResamplingState V T ι) (selector d : ℕ) (i : ι)
    (e : I ↪ {v : (Tᶜ : Set V) // v ≠ s.sampledOutsideFirst i})
    (hcapture : s.otherOutsideEndpoints selector i ⊆ Set.range e) (z : ℂ) (hz : 0 < z.im) :
    let H := deletedMatrix (normalizedAdjacency (outsideGraph s.graph T) d) (s.sampledOutsideFirst i)
    let K := deletedMatrix (normalizedAdjacency (outsideGraph (s.fullResample selector).graph T) d) (s.sampledOutsideFirst i)
    let R := (green H z).submatrix e e
    let U := (green K z).submatrix e e
    let W := (K - H).submatrix e e
    (U + R * W * U = R) ∧ (U + U * W * R = R) := by
  apply green_embedded_finite_rank_updates _ _
    (deletedMatrix_isHermitian _ (normalizedAdjacency_isHermitian _ _) _)
    (deletedMatrix_isHermitian _ (normalizedAdjacency_isHermitian _ _) _) e _ z hz
  intro x y hxy
  apply s.fullResample_minor_difference_supported selector d i x y
  exact hxy.imp (fun hx hs => hx (hcapture hs)) (fun hy hs => hy (hcapture hs))

end LabelledResamplingState
end LocalLaw
