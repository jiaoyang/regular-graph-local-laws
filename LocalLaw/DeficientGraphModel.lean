import LocalLaw.GraphModel
import LocalLaw.BoundaryResolvent
import LocalLaw.PrincipalDeletion
import LocalLaw.LocalResamplingData

/-!
# Finite graphs with the source deficit convention

A deficit is allowed whenever degree(v)+deficit(v)<=d. Taking an induced
neighborhood restricts that deficit; deleting vertices increases it by the
actual lost degree, as in (2.8). Both operations and their extension matrices
are defined here, including the genuine deleted-graph and regular-graph
specializations. The averaged Q remains that of the original regular graph.
-/

noncomputable section
namespace LocalLaw

local instance deficientModelDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- The source Definition 2.3, using the equivalent additive degree budget. -/
structure DeficientGraph (V : Type*) [Fintype V] (d : ℕ) where
  graph : SimpleGraph V
  deficit : V → ℕ
  degree_deficit_le : ∀ v, graph.degree v + deficit v ≤ d

section GraphMatrices

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
/-- Normalization commutes with actual induced restriction, with no padding
by deleted zero rows. -/
theorem normalizedAdjacency_induce (G : SimpleGraph V) (d : ℕ) (S : Set V) :
    normalizedAdjacency (G.induce S) d =
      (normalizedAdjacency G d).submatrix (Subtype.val : S → V) (Subtype.val : S → V) := by
  ext i j
  simp only [normalizedAdjacency, Matrix.smul_apply, Matrix.submatrix_apply,
    smul_eq_mul, SimpleGraph.adjMatrix_apply]
  rfl

end GraphMatrices

namespace DeficientGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {d : ℕ}

omit [DecidableEq V] in
theorem degree_le (g : DeficientGraph V d) (v : V) : g.graph.degree v ≤ d :=
  (Nat.le_add_right _ _).trans (g.degree_deficit_le v)

omit [DecidableEq V] in
theorem deficit_le (g : DeficientGraph V d) (v : V) : g.deficit v ≤ d :=
  (Nat.le_add_left _ _).trans (g.degree_deficit_le v)

def H (g : DeficientGraph V d) : Matrix V V ℂ := normalizedAdjacency g.graph d

def G (g : DeficientGraph V d) (z : ℂ) : Matrix V V ℂ := green g.H z

/-- The exact real diagonal coefficient in (2.11). -/
def boundaryCoefficient (g : DeficientGraph V d) (v : V) : ℝ :=
  ((d : ℝ) - (g.deficit v : ℝ) - (g.graph.degree v : ℝ)) / ((d : ℝ) - 1)

omit [DecidableEq V] in
theorem boundaryCoefficient_nonnegative (g : DeficientGraph V d) (hd : 3 ≤ d) (v : V) :
    0 ≤ g.boundaryCoefficient v := by
  have hdeg : (g.graph.degree v : ℝ) + (g.deficit v : ℝ) ≤ d := by
    exact_mod_cast g.degree_deficit_le v
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  exact div_nonneg (by linarith) (by linarith)

omit [DecidableEq V] in
theorem boundaryCoefficient_le_two (g : DeficientGraph V d) (hd : 3 ≤ d) (v : V) :
    g.boundaryCoefficient v ≤ 2 := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  apply (div_le_iff₀ (show 0 < (d : ℝ) - 1 by linarith)).mpr
  dsimp [boundaryCoefficient]
  have hδ : (0 : ℝ) ≤ g.deficit v := Nat.cast_nonneg _
  have hdeg : (0 : ℝ) ≤ g.graph.degree v := Nat.cast_nonneg _
  linarith

def boundaryDiagonal (g : DeficientGraph V d) : Matrix V V ℂ :=
  Matrix.diagonal (fun v => (g.boundaryCoefficient v : ℂ))

theorem boundaryDiagonal_eq_source (g : DeficientGraph V d) :
    g.boundaryDiagonal = boundaryDeficitMatrix d g.deficit (fun v => g.graph.degree v) := rfl

def extensionMatrix (g : DeficientGraph V d) (w z : ℂ) : Matrix V V ℂ :=
  boundaryMatrix g.H g.boundaryDiagonal w z

def extensionGreen (g : DeficientGraph V d) (w z : ℂ) : Matrix V V ℂ :=
  boundaryGreen g.H g.boundaryDiagonal w z

theorem extensionMatrix_isUnit (g : DeficientGraph V d) (hd : 3 ≤ d)
    (w z : ℂ) (hz : 0 < z.im) (hw : 0 ≤ w.im) : IsUnit (g.extensionMatrix w z) :=
  boundaryMatrix_isUnit g.H (normalizedAdjacency_isHermitian g.graph d)
    g.boundaryCoefficient (g.boundaryCoefficient_nonnegative hd) w z hz hw

theorem extensionGreen_diagonal_im_nonnegative (g : DeficientGraph V d) (hd : 3 ≤ d)
    (w z : ℂ) (hz : 0 < z.im) (hw : 0 ≤ w.im) (v : V) :
    0 ≤ (g.extensionGreen w z v v).im :=
  boundaryGreen_diagonal_im_nonneg g.H (normalizedAdjacency_isHermitian g.graph d)
    g.boundaryCoefficient (g.boundaryCoefficient_nonnegative hd) w z hz hw v

theorem extensionGreen_entry_norm_le (g : DeficientGraph V d) (hd : 3 ≤ d)
    (w z : ℂ) (hz : 0 < z.im) (hw : 0 ≤ w.im) (i j : V) :
    ‖g.extensionGreen w z i j‖ ≤ 1 / z.im :=
  boundaryGreen_entry_norm_le g.H (normalizedAdjacency_isHermitian g.graph d)
    g.boundaryCoefficient (g.boundaryCoefficient_nonnegative hd) w z hz hw i j

/-- Coarse two-variable continuity also applies to every correctly deficient
model; the factor eta0^(-2) is explicit. -/
theorem extensionGreen_entry_lipschitz (g : DeficientGraph V d) (hd : 3 ≤ d)
    (u v z w : ℂ) (η₀ : ℝ) (hη₀ : 0 < η₀)
    (hz : η₀ ≤ z.im) (hw : η₀ ≤ w.im) (hu : 0 ≤ u.im) (hv : 0 ≤ v.im)
    (i j : V) :
    ‖g.extensionGreen u z i j - g.extensionGreen v w i j‖ ≤
      (dist z w + 2 * dist u v) / η₀ ^ 2 :=
  boundaryGreen_entry_lipschitz g.H (normalizedAdjacency_isHermitian g.graph d)
    g.boundaryCoefficient (g.boundaryCoefficient_nonnegative hd) 2 (by norm_num)
    (g.boundaryCoefficient_le_two hd) u v z w η₀ hη₀ hz hw hu hv i j

/-- Induced neighborhoods keep the original deficit (Remark 2.5). -/
def restrict (g : DeficientGraph V d) (S : Set V) : DeficientGraph S d where
  graph := g.graph.induce S
  deficit := fun v => g.deficit v.val
  degree_deficit_le := by
    intro v
    have hdeg := induced_degree_le g.graph S v
    have hbudget := g.degree_deficit_le v.val
    simp only [SimpleGraph.degree, SimpleGraph.neighborFinset, Set.toFinset_card,
      ← Nat.card_eq_fintype_card] at hdeg hbudget ⊢
    omega

/-- Actual vertex deletion increases the deficit by the actual lost degree,
exactly the convention (2.8), including preexisting nonzero deficits. -/
def delete (g : DeficientGraph V d) (T : Set V) : DeficientGraph (Tᶜ : Set V) d where
  graph := g.graph.induce Tᶜ
  deficit := fun v => g.deficit v.val + g.graph.degree v.val - (g.graph.induce Tᶜ).degree v
  degree_deficit_le := by
    intro v
    have hdeg := induced_degree_le g.graph Tᶜ v
    have hbudget := g.degree_deficit_le v.val
    simp only [SimpleGraph.degree, SimpleGraph.neighborFinset, Set.toFinset_card,
      ← Nat.card_eq_fintype_card] at hdeg hbudget ⊢
    omega

omit [DecidableEq V] in
theorem delete_deficit (g : DeficientGraph V d) (T : Set V) (v : (Tᶜ : Set V)) :
    (g.delete T).deficit v = g.deficit v.val +
      (g.graph.degree v.val - (g.graph.induce Tᶜ).degree v) := by
  have hdeg := induced_degree_le g.graph Tᶜ v
  simp only [delete, SimpleGraph.degree, SimpleGraph.neighborFinset, Set.toFinset_card,
    ← Nat.card_eq_fintype_card] at hdeg ⊢
  omega

omit [DecidableEq V] in
/-- Deletion keeps the number of attached external branches fixed. It
removes only the physical edges incident to deleted vertices. -/
theorem delete_boundaryCoefficient (g : DeficientGraph V d) (T : Set V)
    (v : (Tᶜ : Set V)) :
    (g.delete T).boundaryCoefficient v = g.boundaryCoefficient v.val := by
  have hdeg := induced_degree_le g.graph Tᶜ v
  have htotal : (g.delete T).deficit v + (g.delete T).graph.degree v =
      g.deficit v.val + g.graph.degree v.val := by
    simp only [delete, SimpleGraph.degree, SimpleGraph.neighborFinset, Set.toFinset_card,
      ← Nat.card_eq_fintype_card] at hdeg ⊢
    omega
  have hreal : ((g.delete T).deficit v : ℝ) + ((g.delete T).graph.degree v : ℝ) =
      (g.deficit v.val : ℝ) + (g.graph.degree v.val : ℝ) := by exact_mod_cast htotal
  unfold boundaryCoefficient
  congr 1
  linarith

omit [DecidableEq V] in
theorem H_restrict (g : DeficientGraph V d) (S : Set V) :
    (g.restrict S).H = g.H.submatrix (Subtype.val : S → V) (Subtype.val : S → V) :=
  normalizedAdjacency_induce g.graph d S

omit [DecidableEq V] in
theorem H_delete (g : DeficientGraph V d) (T : Set V) :
    (g.delete T).H =
      g.H.submatrix (Subtype.val : (Tᶜ : Set V) → V) (Subtype.val : (Tᶜ : Set V) → V) :=
  normalizedAdjacency_induce g.graph d Tᶜ

/-- The source deficit adjustment makes the boundary diagonal commute
with actual deletion. -/
theorem boundaryDiagonal_delete (g : DeficientGraph V d) (T : Set V) :
    (g.delete T).boundaryDiagonal = g.boundaryDiagonal.submatrix
      (Subtype.val : (Tᶜ : Set V) → V) (Subtype.val : (Tᶜ : Set V) → V) := by
  ext i j
  simp only [boundaryDiagonal, Matrix.submatrix_apply, Matrix.diagonal_apply,
    delete_boundaryCoefficient]
  by_cases h : i = j
  · subst j; simp
  · have hval : i.val ≠ j.val := fun heq => h (Subtype.ext heq)
    simp [h, hval]

/-- Actual finite extension matrices satisfy the source deletion convention,
so the Schur identities apply to these same physical identifiers. -/
theorem extensionMatrix_delete (g : DeficientGraph V d) (T : Set V) (w z : ℂ) :
    (g.delete T).extensionMatrix w z = (g.extensionMatrix w z).submatrix
      (Subtype.val : (Tᶜ : Set V) → V) (Subtype.val : (Tᶜ : Set V) → V) := by
  change spectralMatrix (g.delete T).H z - w • (g.delete T).boundaryDiagonal =
    (spectralMatrix g.H z - w • g.boundaryDiagonal).submatrix
      (Subtype.val : (Tᶜ : Set V) → V) (Subtype.val : (Tᶜ : Set V) → V)
  rw [H_delete, boundaryDiagonal_delete, spectralMatrix_principal g.H z
    (Subtype.val : (Tᶜ : Set V) → V) Subtype.val_injective]
  rfl

/-- The exact arbitrary-set model Schur identity, with the full and deleted
units derived from their Hermitian dissipative matrices. -/
theorem extensionGreen_delete (g : DeficientGraph V d) (hd : 3 ≤ d)
    (T : Set V) (w z : ℂ) (hz : 0 < z.im) (hw : 0 ≤ w.im) :
    (g.delete T).extensionGreen w z =
      (g.extensionGreen w z).submatrix
        (Subtype.val : (Tᶜ : Set V) → V) (Subtype.val : (Tᶜ : Set V) → V) -
      (g.extensionGreen w z).submatrix
        (Subtype.val : (Tᶜ : Set V) → V) (Subtype.val : T → V) *
      ((g.extensionGreen w z).submatrix (Subtype.val : T → V) (Subtype.val : T → V))⁻¹ *
      (g.extensionGreen w z).submatrix
        (Subtype.val : T → V) (Subtype.val : (Tᶜ : Set V) → V) := by
  have hunit := g.extensionMatrix_isUnit hd w z hz hw
  have hdeleted := (g.delete T).extensionMatrix_isUnit hd w z hz hw
  rw [extensionMatrix_delete] at hdeleted
  have h := deleted_principal_inverse T (g.extensionMatrix w z) hunit hdeleted
  rw [← extensionMatrix_delete] at h
  exact h

/-- The actual Green function of G(T), identified with the set-deleted
principal resolvent, not a new inverse assumption. -/
theorem G_delete (g : DeficientGraph V d) (T : Set V) (z : ℂ) (hz : 0 < z.im) :
    (g.delete T).G z =
      (g.G z).submatrix (Subtype.val : (Tᶜ : Set V) → V) (Subtype.val : (Tᶜ : Set V) → V) -
      (g.G z).submatrix (Subtype.val : (Tᶜ : Set V) → V) (Subtype.val : T → V) *
      ((g.G z).submatrix (Subtype.val : T → V) (Subtype.val : T → V))⁻¹ *
      (g.G z).submatrix (Subtype.val : T → V) (Subtype.val : (Tᶜ : Set V) → V) := by
  rw [G, H_delete]
  exact green_deleted_principal T g.H (normalizedAdjacency_isHermitian _ _) z hz

/-- The actual pair-ball extension model for a graph carrying a deficit. -/
def P (g : DeficientGraph V d) (r : ℕ) (z w : ℂ) (i j : V) : ℂ :=
  (g.restrict (pairBallVertices g.graph i j r)).extensionGreen w z
    (pairBallLeft g.graph i j r) (pairBallRight g.graph i j r)

theorem pairExtensionMatrix_isUnit (g : DeficientGraph V d) (hd : 3 ≤ d)
    (r : ℕ) (z w : ℂ) (hz : 0 < z.im) (hw : 0 ≤ w.im) (i j : V) :
    IsUnit ((g.restrict (pairBallVertices g.graph i j r)).extensionMatrix w z) :=
  (g.restrict _).extensionMatrix_isUnit hd w z hz hw

/-- Coarse continuity for the actual pair-ball model with inherited deficit. -/
theorem P_lipschitz (g : DeficientGraph V d) (hd : 3 ≤ d) (r : ℕ)
    (u v z w : ℂ) (η₀ : ℝ) (hη₀ : 0 < η₀)
    (hz : η₀ ≤ z.im) (hw : η₀ ≤ w.im) (hu : 0 ≤ u.im) (hv : 0 ≤ v.im)
    (i j : V) :
    ‖g.P r z u i j - g.P r w v i j‖ ≤ (dist z w + 2 * dist u v) / η₀ ^ 2 :=
  (g.restrict _).extensionGreen_entry_lipschitz hd u v z w η₀ hη₀ hz hw hu hv _ _

end DeficientGraph

namespace RegularGraph

variable {N d : ℕ}

/-- Original regular graphs carry the zero deficit. -/
def deficient (g : RegularGraph N d) : DeficientGraph (Fin N) d where
  graph := g.graph
  deficit := fun _ => 0
  degree_deficit_le := by intro v; simpa only [Nat.add_zero] using (g.regular v).le

theorem deficient_P (g : RegularGraph N d) (r : ℕ) (z w : ℂ) (i j : Fin N) :
    g.deficient.P r z w i j = g.P r z w i j := by
  simp only [DeficientGraph.P, DeficientGraph.restrict, DeficientGraph.extensionGreen,
    DeficientGraph.H, DeficientGraph.boundaryDiagonal, DeficientGraph.boundaryCoefficient,
    deficient, RegularGraph.P, pairBoundaryCoefficient, pairBallGraph, Nat.cast_zero, sub_zero]

/-- On deleting vertices from an actual regular graph, the source deficit
is exactly the actual lost degree d-degree_G(T). -/
theorem deleted_deficient_deficit (g : RegularGraph N d) (T : Set (Fin N))
    (v : (Tᶜ : Set (Fin N))) :
    (g.deficient.delete T).deficit v = d - (g.graph.induce Tᶜ).degree v := by
  change 0 + g.graph.degree v.val - (g.graph.induce Tᶜ).degree v = _
  rw [g.regular]
  simp only [Nat.zero_add]

/-- The ambient deleted graph has no artificial boundary loops: its full
extension matrix is its actual spectral matrix for every boundary weight. -/
theorem deleted_deficient_boundaryCoefficient (g : RegularGraph N d)
    (T : Set (Fin N)) (v : (Tᶜ : Set (Fin N))) :
    (g.deficient.delete T).boundaryCoefficient v = 0 := by
  rw [DeficientGraph.delete_boundaryCoefficient]
  have hdeg : g.deficient.graph.degree v.val = d := by
    have h := g.regular v.val
    simpa only [deficient, SimpleGraph.degree, SimpleGraph.neighborFinset,
      Set.toFinset_card, ← Nat.card_eq_fintype_card] using h
  unfold DeficientGraph.boundaryCoefficient
  rw [hdeg]
  simp [deficient]

theorem deleted_deficient_extensionGreen (g : RegularGraph N d) (T : Set (Fin N))
    (w z : ℂ) :
    (g.deficient.delete T).extensionGreen w z =
      green (normalizedAdjacency (g.graph.induce Tᶜ) d) z := by
  have hD : (g.deficient.delete T).boundaryDiagonal = 0 := by
    ext i j
    simp [DeficientGraph.boundaryDiagonal, g.deleted_deficient_boundaryCoefficient T]
  simp only [DeficientGraph.extensionGreen, hD, boundaryGreen, boundaryMatrix,
    smul_zero, sub_zero]
  rfl

/-- The deleted Green function is the same actual outside-graph Green
function used by Ward counting and the cavity observations. -/
theorem deleted_deficient_G (g : RegularGraph N d) (T : Set (Fin N)) (z : ℂ) :
    (g.deficient.delete T).G z = green (normalizedAdjacency (outsideGraph g.graph T) d) z := by
  rfl

/-- The source finite pair model in G(T), with its correctly increased
nonzero deficit and the original graph's boundary parameter supplied later. -/
def deletedP (g : RegularGraph N d) (T : Set (Fin N)) (r : ℕ)
    (z w : ℂ) (i j : (Tᶜ : Set (Fin N))) : ℂ :=
  (g.deficient.delete T).P r z w i j

/-- In particular the deleted-graph local model at the original random Q
has a genuine inverse; no local-law assumption is used for nonsingularity. -/
theorem deleted_pairMatrix_Q_isUnit (g : RegularGraph N d) (hd : 3 ≤ d)
    (T : Set (Fin N)) (r : ℕ) (z : ℂ) (hz : 0 < z.im)
    (i j : (Tᶜ : Set (Fin N))) :
    IsUnit (((g.deficient.delete T).restrict
      (pairBallVertices (g.deficient.delete T).graph i j r)).extensionMatrix (g.Q z) z) :=
  (g.deficient.delete T).pairExtensionMatrix_isUnit hd r z (g.Q z) hz
    (g.Q_im_nonnegative z hz) i j

/-- In a deleted-graph neighborhood, its coefficient counts only the
boundary edges of G(T); lost original edges are accounted for in the deficit. -/
theorem deleted_pair_boundaryCoefficient (g : RegularGraph N d) (T : Set (Fin N))
    (S : Set (Tᶜ : Set (Fin N))) (v : S) :
    ((g.deficient.delete T).restrict S).boundaryCoefficient v =
      (((g.graph.induce Tᶜ).degree v.val : ℝ) -
        (((g.graph.induce Tᶜ).induce S).degree v : ℝ)) / ((d : ℝ) - 1) := by
  have hdeg := induced_degree_le g.graph Tᶜ v.val
  have hdeg' : (g.graph.induce Tᶜ).degree v.val ≤ d := by
    have h := hdeg.trans_eq (g.regular _)
    simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset, Set.toFinset_card,
      ← Nat.card_eq_fintype_card] using h
  have hcast := Nat.cast_sub hdeg' (R := ℝ)
  change ((d : ℝ) - ((g.deficient.delete T).deficit v.val : ℝ) -
    (((g.graph.induce Tᶜ).induce S).degree v : ℝ)) / _ = _
  rw [g.deleted_deficient_deficit, hcast]
  congr 1
  ring

end RegularGraph

end LocalLaw
