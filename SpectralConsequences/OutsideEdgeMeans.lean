import SpectralConsequences.RegularEdgeMeans
import SpectralConsequences.FiniteRestrictionMeans

/-! # The actual outside-edge sampling bias

The directed-edge restriction costs O(|T|/N), with an explicit constant.
Together with the exact constant-vector Green row sum this proves the
unrestricted-resolvent part of the conditional means in Section 7.1.
-/
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1200000
namespace SpectralConsequences
open LocalLaw
local instance outsideEdgeMeansDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {E F : Type*} [Fintype E] [Fintype F]

theorem finiteComplexMean_equiv (e : E ≃ F) (f : F → ℂ) :
    finiteComplexMean (fun x => f (e x)) = finiteComplexMean f := by
  unfold finiteComplexMean
  rw [Fintype.card_congr e]
  congr 1
  apply Fintype.sum_equiv e
  intro _
  rfl

variable {V : Type*}

/-- Outside oriented edges are exactly darts with both endpoints outside T. -/
def outsideDartEquiv (G : SimpleGraph V) (T : Set V) :
    OutsideOrientedEdge G T ≃ {e : G.Dart // e.fst ∉ T ∧ e.snd ∉ T} where
  toFun e := ⟨⟨e.val,e.property.1⟩,e.property.2⟩
  invFun e := ⟨e.val.toProd,e.val.adj,e.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

namespace RegularGraph
variable {N d : ℕ}

/-- The number of excluded darts is at most twice d times the removed vertex
count, with no graph-size asymptotic or probability premise. -/
theorem excluded_darts_card (g : LocalLaw.RegularGraph N d) (T : Set (Fin N)) :
    Nat.card {e : g.graph.Dart // ¬(e.fst ∉ T ∧ e.snd ∉ T)} ≤ 2*d*Nat.card T := by
  have hsub := Fintype.card_subtype_compl
    (fun e : g.graph.Dart => e.fst ∉ T ∧ e.snd ∉ T)
  have he : Nat.card {e : g.graph.Dart // e.fst ∉ T ∧ e.snd ∉ T} =
      Nat.card (OutsideOrientedEdge g.graph T) := Nat.card_congr (outsideDartEquiv g.graph T).symm
  have hfull := g.oriented_edge_count
  have hc := g.outside_count_identity T
  have ht := g.boundary_interior_count T
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    ← Nat.card_eq_fintype_card, he, hfull] at hsub
  rw [hsub]
  apply Nat.sub_le_iff_le_add.mpr
  nlinarith

/-- Independent outside-edge samples recover the trivial-pole average,
up to an explicit removed-vertex-density error. -/
theorem outside_second_green_mean (g : LocalLaw.RegularGraph N d)
    (T : Set (Fin N)) (hN : 0 < N) (hd : 0 < d) (hT : 4*Nat.card T ≤ N)
    (z : ℂ) (hz : 0 < z.im) (C : ℝ) (hC : 0 ≤ C)
    (hG : ∀ i j, ‖g.G z i j‖ ≤ C) :
    ‖finiteComplexMean (fun e : OutsideOrientedEdge g.graph T =>
        finiteComplexMean (fun f : OutsideOrientedEdge g.graph T =>
          g.G z e.val.2 f.val.2)) -
      (N : ℂ)⁻¹ * (treeEdgeWeight d * (d : ℂ)-z)⁻¹‖ ≤
      8*C*(Nat.card T : ℝ)/(N : ℝ) := by
  let A : g.graph.Dart → Prop := fun e => e.fst ∉ T ∧ e.snd ∉ T
  letI : Nonempty (OutsideOrientedEdge g.graph T) := g.outside_edge_nonempty T hN hd hT
  letI : Nonempty g.graph.Dart :=
    ⟨((outsideDartEquiv g.graph T) (Classical.choice inferInstance)).val⟩
  letI : Nonempty {e : g.graph.Dart // A e} :=
    ⟨(outsideDartEquiv g.graph T) (Classical.choice inferInstance)⟩
  have hres := finiteComplexMean_restriction_pair_difference A
    (fun e f : g.graph.Dart => g.G z e.snd f.snd) C hC (fun e f => hG e.snd f.snd)
  have hid : finiteComplexMean (fun e : OutsideOrientedEdge g.graph T =>
      finiteComplexMean (fun f : OutsideOrientedEdge g.graph T => g.G z e.val.2 f.val.2)) =
    finiteComplexMean (fun e : {e : g.graph.Dart // A e} =>
      finiteComplexMean (fun f : {e : g.graph.Dart // A e} => g.G z e.val.snd f.val.snd)) := by
    calc
      _ = finiteComplexMean (fun e : OutsideOrientedEdge g.graph T =>
          finiteComplexMean (fun f : {e : g.graph.Dart // A e} => g.G z e.val.2 f.val.snd)) := by
        congr 1
        funext e
        exact finiteComplexMean_equiv (outsideDartEquiv g.graph T)
          (fun f : {e : g.graph.Dart // A e} => g.G z e.val.2 f.val.snd)
      _ = _ := finiteComplexMean_equiv (outsideDartEquiv g.graph T)
        (fun e : {e : g.graph.Dart // A e} => finiteComplexMean
          (fun f : {e : g.graph.Dart // A e} => g.G z e.val.snd f.val.snd))
  rw [independent_second_green_mean g hN hd z hz, ← hid, norm_sub_rev] at hres
  apply hres.trans
  have hcard := excluded_darts_card g T
  have hcardR : (Nat.card {e : g.graph.Dart // ¬A e} : ℝ) ≤ 2*(d:ℝ)*(Nat.card T:ℝ) := by
    exact_mod_cast hcard
  have hcount : (Fintype.card g.graph.Dart : ℝ) = (N:ℝ)*(d:ℝ) := by
    have hh := g.oriented_edge_count
    rw [Nat.card_eq_fintype_card] at hh
    exact_mod_cast hh
  rw [hcount]
  calc
    _ ≤ 4*C*(2*(d:ℝ)*(Nat.card T:ℝ))/((N:ℝ)*(d:ℝ)) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hcardR (by positivity)
    _ = _ := by
      have hn : (N:ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hN
      have hdn : (d:ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hd
      field_simp
      ring

end RegularGraph
end SpectralConsequences
