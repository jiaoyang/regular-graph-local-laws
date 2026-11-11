import LocalLaw.BoundedGraphOperator

/-! # Genuine Green functions on a neighbor-closed embedded graph

Restriction along an injection preserves square summability. When the image
is closed under ambient neighbors and adjacency is reflected, the restricted
ambient resolvent column solves the source resolvent equation. Uniqueness of
the genuine bounded-operator inverse gives entry equality. No spectral or
Green-function identification is assumed.
-/

open scoped BigOperators Topology ENNReal
noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
namespace SpectralConsequences
open LocalLaw
local instance graphGreenEmbeddingDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

def graphL2Pullback (e : V ↪ W) (f : GraphL2 W) : GraphL2 V :=
  ⟨fun v => f (e v), memℓp_gen' (C := ‖f‖^2) (fun S => by
    have hh := lp.sum_rpow_le_norm_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal) f (S.image e)
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hh ⊢
    rw [Finset.sum_image] at hh
    · exact hh
    · intro a _ b _ hab
      exact e.injective hab)⟩

omit [DecidableEq V] in
theorem graphL2Pullback_apply (e : V ↪ W) (f : GraphL2 W) (v : V) :
    graphL2Pullback e f v = f (e v) := rfl

theorem graphL2Pullback_single (e : V ↪ W) (j : V) :
    graphL2Pullback e (lp.single 2 (e j) 1) = lp.single 2 j 1 := by
  apply lp.ext
  funext v
  simp only [graphL2Pullback_apply, lp.single_apply, Pi.single_apply]
  simp only [e.injective.eq_iff]

variable (G : SimpleGraph V) [G.LocallyFinite]
    (H : SimpleGraph W) [H.LocallyFinite] (e : V ↪ W)
    (hAdj : ∀ i j, H.Adj (e i) (e j) ↔ G.Adj i j)
    (hClosed : ∀ i w, H.Adj (e i) w → ∃ j, e j = w)

include hAdj hClosed

omit [DecidableEq V] in
theorem embedded_neighborFinset (i : V) :
    (G.neighborFinset i).image e = H.neighborFinset (e i) := by
  ext w
  simp only [Finset.mem_image, SimpleGraph.mem_neighborFinset]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact (hAdj i j).mpr hj
  · intro hw
    obtain ⟨j, rfl⟩ := hClosed i w hw
    exact ⟨j, (hAdj i j).mp hw, rfl⟩

theorem embedded_adjacency_pullback (d : ℕ)
    (hG : ∀ v, G.degree v ≤ d) (hH : ∀ w, H.degree w ≤ d) (f : GraphL2 W) :
    G.boundedAdjacency d hG (graphL2Pullback e f) =
      graphL2Pullback e (H.boundedAdjacency d hH f) := by
  apply lp.ext
  funext v
  rw [G.boundedAdjacency_apply, graphL2Pullback_apply, H.boundedAdjacency_apply,
    ← embedded_neighborFinset G H e hAdj hClosed v]
  rw [Finset.sum_image]
  · rfl
  · intro a _ b _ hab
    exact e.injective hab

theorem embedded_spectral_pullback (d : ℕ)
    (hG : ∀ v, G.degree v ≤ d) (hH : ∀ w, H.degree w ≤ d)
    (z : ℂ) (f : GraphL2 W) :
    G.graphSpectralOperator d hG z (graphL2Pullback e f) =
      graphL2Pullback e (H.graphSpectralOperator d hH z f) := by
  have hh := embedded_adjacency_pullback G H e hAdj hClosed d hG hH f
  apply lp.ext
  funext v
  have hv := congrArg (fun u : GraphL2 V => u v) hh
  simp only [SimpleGraph.graphSpectralOperator, SimpleGraph.normalizedOperator,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
    graphL2Pullback_apply, lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply, Pi.smul_apply] at hv ⊢
  rw [hv]

theorem green_eq_of_neighbor_closed_embedding (d : ℕ)
    (hG : ∀ v, G.degree v ≤ d) (hH : ∀ w, H.degree w ≤ d)
    (z : ℂ) (hz : z.im ≠ 0) (i j : V) :
    H.infiniteGreen d hH z (e i) (e j) = G.infiniteGreen d hG z i j := by
  let f := H.infiniteGreenOperator d hH z (lp.single 2 (e j) 1)
  have hsolve : H.graphSpectralOperator d hH z f = lp.single 2 (e j) 1 :=
    congrArg (fun A : GraphL2 W →L[ℂ] GraphL2 W => A (lp.single 2 (e j) 1))
      (H.infiniteGreenOperator_right_inverse d hH z hz)
  have hpull : G.graphSpectralOperator d hG z (graphL2Pullback e f) = lp.single 2 j 1 := by
    rw [embedded_spectral_pullback G H e hAdj hClosed d hG hH z f, hsolve,
      graphL2Pullback_single]
  have hleft := G.infiniteGreenOperator_left_inverse d hG z hz
  have huniq : G.infiniteGreenOperator d hG z (lp.single 2 j 1) = graphL2Pullback e f := by
    rw [← hpull]
    exact congrArg (fun A : GraphL2 V →L[ℂ] GraphL2 V => A (graphL2Pullback e f)) hleft
  change f (e i) = G.infiniteGreenOperator d hG z (lp.single 2 j 1) i
  rw [huniq]
  rfl

omit hAdj hClosed in
theorem green_eq_of_graph_iso (iso : G ≃g H) (d : ℕ)
    (hG : ∀ v, G.degree v ≤ d) (hH : ∀ w, H.degree w ≤ d)
    (z : ℂ) (hz : z.im ≠ 0) (i j : V) :
    H.infiniteGreen d hH z (iso i) (iso j) = G.infiniteGreen d hG z i j := by
  let emb : V ↪ W := ⟨iso, iso.injective⟩
  exact green_eq_of_neighbor_closed_embedding G H emb
    (fun i j => iso.map_rel_iff')
    (fun _ w _ => ⟨iso.symm w, iso.apply_symm_apply w⟩) d hG hH z hz i j

end SpectralConsequences
