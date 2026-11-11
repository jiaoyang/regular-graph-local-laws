import LocalLaw.RestrictionDeletionIdentity
import LocalLaw.EmbeddedFiniteRankResolvent
import LocalLaw.SourceCavityTreeIdentity

/-!
# The same physical perturbation in actual finite extension models

For a saturated source deficit, restricted boundary charge counts genuine
neighbors outside the restriction. Changing only internal edges preserves
that charge exactly. Old and new extension matrices therefore differ by
the physical normalized-adjacency perturbation, with the same coupling W.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance restrictedPerturbationDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem induced_degree_loss_eq_outside_neighbors (G : SimpleGraph V) (S : Set V) (v : S) :
    G.degree v.val - (G.induce S).degree v = Nat.card {w : (Sᶜ : Set V) // G.Adj w.val v.val} := by
  let vv : ((Sᶜ)ᶜ : Set V) := ⟨v.val, by simpa only [Set.mem_compl_iff, not_not] using v.property⟩
  have hh := degree_loss_eq_removed_neighbor_count G Sᶜ vv
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hh ⊢
  let φ : outsideGraph G Sᶜ ≃g G.induce S :=
    { toFun := fun x => ⟨x.val, not_not.mp x.property⟩
      invFun := fun x => ⟨x.val, fun h => h x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  have hdegree := Nat.card_congr (φ.mapNeighborSet vv)
  change Nat.card ((outsideGraph G Sᶜ).neighborSet vv) = Nat.card ((G.induce S).neighborSet v) at hdegree
  rw [hdegree] at hh
  exact hh

namespace DeficientGraph
variable {d : ℕ}

omit [DecidableEq V] in
theorem restrict_boundaryCoefficient_eq_outside_neighbors (g : DeficientGraph V d) (S : Set V)
    (hsaturated : ∀ v, g.graph.degree v + g.deficit v = d) (v : S) :
    (g.restrict S).boundaryCoefficient v =
      (Nat.card {w : (Sᶜ : Set V) // g.graph.Adj w.val v.val} : ℝ) / ((d : ℝ) - 1) := by
  have hle := induced_degree_le g.graph S v
  have hloss := induced_degree_loss_eq_outside_neighbors g.graph S v
  have hsat := hsaturated v.val
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hle hloss hsat
  have hlossR := congrArg (fun n : ℕ => (n : ℝ)) hloss
  dsimp only at hlossR
  rw [Nat.cast_sub hle] at hlossR
  have hsatR : (Nat.card (g.graph.neighborSet v.val) : ℝ) + (g.deficit v.val : ℝ) = d := by exact_mod_cast hsat
  unfold boundaryCoefficient
  change ((d : ℝ) - (g.deficit v.val : ℝ) - ((g.graph.induce S).degree v : ℝ)) / ((d : ℝ) - 1) = _
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
  congr 1
  linarith

theorem restrict_extensionMatrix_difference (g h : DeficientGraph V d) (S : Set V)
    (hsatG : ∀ v, g.graph.degree v + g.deficit v = d)
    (hsatH : ∀ v, h.graph.degree v + h.deficit v = d)
    (hcross : ∀ v : S, ∀ w : (Sᶜ : Set V), g.graph.Adj v.val w.val ↔ h.graph.Adj v.val w.val)
    (q z : ℂ) :
    (h.restrict S).extensionMatrix q z - (g.restrict S).extensionMatrix q z =
      (h.H - g.H).submatrix (Subtype.val : S → V) (Subtype.val : S → V) := by
  have hcoeff (v : S) : (h.restrict S).boundaryCoefficient v = (g.restrict S).boundaryCoefficient v := by
    rw [g.restrict_boundaryCoefficient_eq_outside_neighbors S hsatG,
      h.restrict_boundaryCoefficient_eq_outside_neighbors S hsatH]
    congr 1
    apply congrArg (fun n : ℕ => (n : ℝ))
    apply Nat.card_congr
    exact
      { toFun := fun w => ⟨w.val, ((hcross v w.val).mpr w.property.symm).symm⟩
        invFun := fun w => ⟨w.val, ((hcross v w.val).mp w.property.symm).symm⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hD : (h.restrict S).boundaryDiagonal = (g.restrict S).boundaryDiagonal := by
    simp only [boundaryDiagonal, hcoeff]
  change (spectralMatrix (h.restrict S).H z - q • (h.restrict S).boundaryDiagonal) -
    (spectralMatrix (g.restrict S).H z - q • (g.restrict S).boundaryDiagonal) = _
  rw [hD, h.H_restrict, g.H_restrict, Matrix.submatrix_sub]
  unfold spectralMatrix
  ext i j
  simp only [Pi.sub_apply, Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- Finite old/new models obey the genuine endpoint inverse updates with
the SAME physical coupling as the ambient graph. No model update identity
or boundary-charge equality is supplied as a hypothesis. -/
theorem restrict_endpoint_inverse_updates {I : Type*} [Fintype I]
    (g h : DeficientGraph V d) (hd : 3 ≤ d) (S : Set V) (e : I ↪ S)
    (hsatG : ∀ v, g.graph.degree v + g.deficit v = d)
    (hsatH : ∀ v, h.graph.degree v + h.deficit v = d)
    (hgraph : ∀ x y, x ∉ Set.range (fun i => (e i).val) ∨ y ∉ Set.range (fun i => (e i).val) →
      (g.graph.Adj x y ↔ h.graph.Adj x y))
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) :
    let f : I ↪ V := ⟨fun i => (e i).val, fun _ _ he => e.injective (Subtype.ext he)⟩
    let P := ((g.restrict S).extensionGreen q z).submatrix e e
    let Q := ((h.restrict S).extensionGreen q z).submatrix e e
    let W := (h.H - g.H).submatrix f f
    (Q + P * W * Q = P) ∧ (Q + Q * W * P = P) := by
  let f : I ↪ V := ⟨fun i => (e i).val, fun _ _ he => e.injective (Subtype.ext he)⟩
  have hcross : ∀ v : S, ∀ w : (Sᶜ : Set V), g.graph.Adj v.val w.val ↔ h.graph.Adj v.val w.val := by
    intro v w
    apply hgraph v.val w.val
    right
    rintro ⟨i, hi⟩
    exact w.property (hi ▸ (e i).property)
  have hmatrix := g.restrict_extensionMatrix_difference h S hsatG hsatH hcross q z
  have hphysical : ∀ x y, x ∉ Set.range f ∨ y ∉ Set.range f → (h.H - g.H) x y = 0 := by
    intro x y hxy
    have hagree := hgraph x y hxy
    simp only [H, normalizedAdjacency, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, SimpleGraph.adjMatrix_apply]
    rw [← hagree, sub_self]
  have hmodel : ∀ x y : S, x ∉ Set.range e ∨ y ∉ Set.range e →
      ((h.restrict S).extensionMatrix q z - (g.restrict S).extensionMatrix q z) x y = 0 := by
    intro x y hxy
    rw [hmatrix]
    apply hphysical x.val y.val
    exact hxy.imp
      (fun hx ⟨i, hi⟩ => hx ⟨i, Subtype.ext hi⟩)
      (fun hy ⟨i, hi⟩ => hy ⟨i, Subtype.ext hi⟩)
  have hupdate := inverse_embedded_finite_rank_updates
    ((g.restrict S).extensionMatrix q z) ((h.restrict S).extensionMatrix q z)
    ((g.restrict S).extensionMatrix_isUnit hd q z hz hq)
    ((h.restrict S).extensionMatrix_isUnit hd q z hz hq) e hmodel
  dsimp only at hupdate
  rw [hmatrix] at hupdate
  exact hupdate

end DeficientGraph
end LocalLaw
