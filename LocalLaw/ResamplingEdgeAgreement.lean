import LocalLaw.ResamplingParentComponents

/-!
# Exact old-edge agreement outside the actual removed parent vertices

The full resampling preserves every labelled exterior triple. Every changed
edge touches such a triple, so two ball vertices outside the actual eligible
exterior set have their original adjacency. This supplies the edge-agreement
input used to localize the cyclic core; it is proved from the actual schedule.
-/

noncomputable section
namespace LocalLaw

local instance resamplingEdgeAgreementDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*}

theorem applySwitches_adj_away_exteriors (L : List (SwitchingQuad V)) (G : SimpleGraph V)
    {x y : V} (haway : ∀ q ∈ L, x ∉ q.exterior ∧ y ∉ q.exterior) :
    (applySwitches L G).Adj x y ↔ G.Adj x y := by
  induction L generalizing G with
  | nil => rfl
  | cons q L ih =>
      have hq := haway q (by simp)
      have hnot : ¬ q.footprint.Adj x y := by
        intro h
        exact (q.footprint_touches_exterior h).elim hq.1 hq.2
      exact (ih (q.apply G) (fun p hp => haway p (by simp [hp]))).trans
        (q.adj_outside_footprint G hnot)

namespace LabelledResamplingState
variable {T : Set V} {ι : Type*}

theorem flip_quad_exterior (s : LabelledResamplingState V T ι) (selector : ℕ) (i j : ι) :
    ((s.flip selector i).quad j).exterior = (s.quad j).exterior := by
  by_cases hi : s.Eligible selector i
  · rw [s.flip_eq_perform selector i hi, s.perform_quad selector i j hi.1 hi.2]
    split_ifs with hji
    · subst j
      exact SwitchingQuad.exterior_inverse _
    · rfl
  · rw [s.flip_eq_self selector i hi]

theorem flips_quad_exterior (s : LabelledResamplingState V T ι) (selector : ℕ)
    (L : List ι) (j : ι) : ((s.flips selector L).quad j).exterior = (s.quad j).exterior := by
  induction L generalizing s with
  | nil => rfl
  | cons i L ih => exact (ih (s.flip selector i)).trans (s.flip_quad_exterior selector i j)

theorem mem_selectedQuads (s : LabelledResamplingState V T ι) (selector : ℕ)
    (L : List ι) (q : SwitchingQuad V) :
    q ∈ s.selectedQuads selector L ↔ ∃ i ∈ L, s.Eligible selector i ∧ s.quad i = q := by
  simp only [selectedQuads, List.mem_map, List.mem_filter, decide_eq_true_eq]
  aesop

variable [Fintype ι]

theorem fullResample_quad_exterior (s : LabelledResamplingState V T ι)
    (selector : ℕ) (i : ι) : ((s.fullResample selector).quad i).exterior = (s.quad i).exterior :=
  s.flips_quad_exterior selector _ i

variable [Fintype V]

omit [Fintype V] in
/-- Old/new adjacency agrees on every edge whose two actual ball vertices
avoid all eligible exterior vertices. -/
theorem fullResample_adj_away_eligibleExterior (s : LabelledResamplingState V T ι)
    (selector r : ℕ) (center : V)
    (x y : graphBallVertices (s.fullResample selector).graph center r)
    (hx : x ∉ (s.fullResample selector).eligibleExteriorInBall selector center r)
    (hy : y ∉ (s.fullResample selector).eligibleExteriorInBall selector center r) :
    ((s.fullResample selector).graph.Adj x.val y.val ↔ s.graph.Adj x.val y.val) := by
  have hAdj := congrArg (fun H : SimpleGraph V => H.Adj x.val y.val)
    (s.fullResample_graph_eq_applySwitches selector)
  apply hAdj.to_iff.trans
  apply applySwitches_adj_away_exteriors
  intro q hq
  obtain ⟨i, _, hi, hqi⟩ := (s.mem_selectedQuads selector _ q).mp hq
  subst q
  have hfinal := (s.fullResample_eligible selector i).mpr hi
  have hext := s.fullResample_quad_exterior selector i
  constructor
  · intro hxi
    apply hx
    exact ⟨i, hfinal, by rwa [hext]⟩
  · intro hyi
    apply hy
    exact ⟨i, hfinal, by rwa [hext]⟩

end LabelledResamplingState
end LocalLaw
