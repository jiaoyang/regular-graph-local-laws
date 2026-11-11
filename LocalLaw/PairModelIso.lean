import LocalLaw.DeficientGraphIso
import LocalLaw.ComponentBallGeometry

/-!
# Exact covariance of finite pair models

An actual graph isomorphism identifies endpoint balls by extended distance.
Matching source deficits then identifies the induced pair operators and
their genuine inverse entries, including for disconnected graphs.
-/

noncomputable section
namespace LocalLaw
local instance pairModelIsoDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

def graphIsoPairBallEquiv (e : H ≃g G) (i j : W) (r : ℕ) :
    pairBallVertices H i j r ≃ pairBallVertices G (e i) (e j) r where
  toFun v := ⟨e v.val, by
    rcases v.property with hv | hv
    · left
      change G.edist (e i) (e v.val) ≤ (r : ℕ∞)
      rw [graphIso_edist e]
      exact hv
    · right
      change G.edist (e j) (e v.val) ≤ (r : ℕ∞)
      rw [graphIso_edist e]
      exact hv⟩
  invFun v := ⟨e.symm v.val, by
    rcases v.property with hv | hv
    · left
      change H.edist i (e.symm v.val) ≤ (r : ℕ∞)
      rw [← graphIso_edist e i (e.symm v.val), e.apply_symm_apply]
      exact hv
    · right
      change H.edist j (e.symm v.val) ≤ (r : ℕ∞)
      rw [← graphIso_edist e j (e.symm v.val), e.apply_symm_apply]
      exact hv⟩
  left_inv v := Subtype.ext (e.symm_apply_apply v.val)
  right_inv v := Subtype.ext (e.apply_symm_apply v.val)

def graphIsoPairBallIso (e : H ≃g G) (i j : W) (r : ℕ) :
    pairBallGraph H i j r ≃g pairBallGraph G (e i) (e j) r where
  toEquiv := graphIsoPairBallEquiv e i j r
  map_rel_iff' := by intro a b; exact e.map_rel_iff'

@[simp] theorem graphIsoPairBallIso_val (e : H ≃g G) (i j : W) (r : ℕ)
    (v : pairBallVertices H i j r) : (graphIsoPairBallIso e i j r v).val = e v.val := rfl

namespace DeficientGraph
variable [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] {d : ℕ}

/-- Actual finite pair Green values transport through a source-deficit
preserving graph isomorphism; no entry equality is assumed. -/
theorem P_iso (g : DeficientGraph V d) (h : DeficientGraph W d)
    (e : h.graph ≃g g.graph) (hdeficit : ∀ v, h.deficit v = g.deficit (e v))
    (r : ℕ) (q z : ℂ) (i j : W) : h.P r z q i j = g.P r z q (e i) (e j) := by
  let φ := graphIsoPairBallIso e i j r
  let hm := h.restrict (pairBallVertices h.graph i j r)
  let gm := g.restrict (pairBallVertices g.graph (e i) (e j) r)
  have hdef : ∀ v, hm.deficit v = gm.deficit (φ v) := fun v => hdeficit v.val
  have hh := gm.extensionGreen_iso hm φ hdef q z
  exact (congrFun (congrFun hh (pairBallLeft h.graph i j r)) (pairBallRight h.graph i j r)).symm

end DeficientGraph
end LocalLaw
