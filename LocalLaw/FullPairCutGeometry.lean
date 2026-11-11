import LocalLaw.ResamplingBallPreservation
import LocalLaw.GraphPowerLocality

/-! Omitting any point of the inner ball forces both full pair roots far away. -/
noncomputable section
namespace LocalLaw
local instance fullPairCutGeometryDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type}

theorem inner_ball_subset_pair_of_near_point (G : SimpleGraph V) (o x y : V)
    (ell r m : ℕ) (hm : m+2*ell≤r) (t : V)
    (ht : t∈graphBallVertices G o ell) (hxt : G.edist x t ≤ (m : ℕ∞)) :
    graphBallVertices G o ell⊆pairBallVertices G x y r := by
  intro v hv
  apply Or.inl
  change G.edist x v≤(r:ℕ∞)
  have hto : G.edist t o≤(ell:ℕ∞) := by
    simpa only [SimpleGraph.edist_comm] using ht
  have hvo : G.edist o v≤(ell:ℕ∞) := hv
  calc
    _ ≤ G.edist x t+G.edist t v := G.edist_triangle
    _ ≤ (m:ℕ∞)+((ell:ℕ∞)+(ell:ℕ∞)) := add_le_add hxt
      (((SimpleGraph.edist_triangle (G:=G) (u:=t) (v:=o) (w:=v))).trans (add_le_add hto hvo))
    _ = ((m+2*ell:ℕ):ℕ∞) := by push_cast; ring
    _ ≤ _ := ENat.coe_le_coe.mpr hm

theorem pair_omits_inner_ball_roots_far (G : SimpleGraph V) (o x y : V)
    (ell r m : ℕ) (hm : m+2*ell≤r)
    (hcut : ¬graphBallVertices G o ell⊆pairBallVertices G x y r) :
    ∀t∈graphBallVertices G o ell,(m:ℕ∞)<G.edist x t ∧ (m:ℕ∞)<G.edist y t := by
  intro t ht
  constructor
  · exact lt_of_not_ge (fun hxt=>hcut (inner_ball_subset_pair_of_near_point G o x y ell r m hm t ht hxt))
  · apply lt_of_not_ge
    intro hyt
    have hh:=inner_ball_subset_pair_of_near_point G o y x ell r m hm t ht hyt
    apply hcut
    intro v hv
    exact (hh hv).elim Or.inr Or.inl

namespace LabelledResamplingState
variable {T : Set V} {ι : Type} [Fintype ι]

theorem full_pair_omits_T_roots_far (s : LabelledResamplingState V T ι)
    (selector ell r m : ℕ) (o x y : V)
    (hT : T=graphBallVertices s.graph o ell) (hm : m+2*ell≤r)
    (hcut : ¬T⊆pairBallVertices (s.fullResample selector).graph x y r) :
    ∀t∈T,(m:ℕ∞)<(s.fullResample selector).graph.edist x t ∧
      (m:ℕ∞)<(s.fullResample selector).graph.edist y t := by
  have hball:graphBallVertices (s.fullResample selector).graph o ell=T:=by
    simpa only [graphSetBall_singleton] using s.fullResample_ball selector {o} ell
      (by simpa only [graphSetBall_singleton] using hT)
  have hcut' : ¬graphBallVertices (s.fullResample selector).graph o ell ⊆
      pairBallVertices (s.fullResample selector).graph x y r := by
    intro hh
    exact hcut (fun v hv=>hh (hball.symm ▸ hv))
  intro t ht
  exact pair_omits_inner_ball_roots_far _ o x y ell r m hm hcut' t (hball.symm ▸ ht)

end LabelledResamplingState
end LocalLaw
