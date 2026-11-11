import LocalLaw.ResamplingBallPreservation

/-! # The actual root neighbor set is fixed by boundary resampling -/

namespace LocalLaw
namespace LabelledResamplingState
variable {V : Type*} {T : Set V} {ι : Type*} [Fintype ι]

theorem fullResample_neighborSet_eq (s : LabelledResamplingState V T ι) (selector : ℕ)
    (o : V) (ell : ℕ) (hell : 1≤ell) (hT : T=graphBallVertices s.graph o ell) :
    (s.fullResample selector).graph.neighborSet o=s.graph.neighborSet o := by
  let t := s.fullResample selector
  have hnew : graphBallVertices t.graph o ell=T := by
    simpa only [graphSetBall_singleton] using s.fullResample_ball selector {o} ell
      (by simpa only [graphSetBall_singleton] using hT)
  have ho : o∈T := hT ▸ center_mem_graphBall s.graph o ell
  have holdmem (v : V) (h : s.graph.Adj o v) : v∈T := by
    rw [hT]
    change s.graph.edist o v≤(ell:ℕ∞)
    rw [SimpleGraph.edist_eq_one_iff_adj.mpr h]
    exact_mod_cast hell
  have hnewmem (v : V) (h : t.graph.Adj o v) : v∈T := by
    rw [←hnew]
    change t.graph.edist o v≤(ell:ℕ∞)
    rw [SimpleGraph.edist_eq_one_iff_adj.mpr h]
    exact_mod_cast hell
  have hagree (v : V) (hv : v∈T) : t.graph.Adj o v↔s.graph.Adj o v :=
    Iff.of_eq (congrArg (fun H : SimpleGraph T => H.Adj ⟨o,ho⟩ ⟨v,hv⟩) (s.fullResample_induce selector))
  ext v
  change t.graph.Adj o v↔s.graph.Adj o v
  exact ⟨fun h => (hagree v (hnewmem v h)).mp h,fun h => (hagree v (holdmem v h)).mpr h⟩

end LabelledResamplingState
end LocalLaw
