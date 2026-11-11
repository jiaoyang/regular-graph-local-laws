import LocalLaw.FiniteStarGeometry
import LocalLaw.QuarterCutDichotomy
import LocalLaw.FullOldTwoTargetGeometry

/-! # Literal core geometry for near-T full-model restoration

The core is exactly the two exterior targets together with all exterior
neighbors of T. It is captured by both genuine full models and inherits
the quarter-close distance margin without a cardinality restriction on T.
-/
noncomputable section
namespace LocalLaw
local instance nearCutStarGeometryDecidable (p:Prop):Decidable p:=Classical.propDecidable p
variable {V:Type}

structure NearCutStarGeometry (G:SimpleGraph V)(T S0 S1 I:Set V)(x y:V)(loss:ℕ):Prop where
  core_in_local:I⊆S1
  local_in_common:S1⊆S0
  core_outside:∀v∈I,v∉T
  inner_in_common:T⊆S0
  inner_in_local:T⊆S1
  cut_neighbors:∀t∈T,∀v,G.Adj t v→v∉T→v∈I
  left_target:x∈I ∨ x∈T
  right_target:y∈I ∨ y∈T
  near:∀v∈I,G.edist x v≤(loss:ℕ∞) ∨ G.edist y v≤(loss:ℕ∞)

variable [Fintype V][DecidableEq V]

theorem finiteStarCoreSet_subset_cut_region (G:SimpleGraph V)(T:Set V)(x y:V):
    finiteStarCoreSet G T x y⊆graphSetBall G T 1∪{x,y}:=by
  apply finiteStarCoreSet_subset
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
  · intro t ht v htv
    exact Or.inl ⟨t,ht,(SimpleGraph.edist_eq_one_iff_adj.mpr htv).le⟩

theorem near_cut_star_geometry (G:SimpleGraph V)(T S0 S1:Set V)(x y:V)(r loss:ℕ)
    (hpair:S1=pairBallVertices G x y r)(hsub:S1⊆S0)
    (hcap:graphSetBall G T 1⊆S1)
    (hnear:∀v∈graphSetBall G T 1∪{x,y},G.edist x v≤(loss:ℕ∞) ∨ G.edist y v≤(loss:ℕ∞)):
    NearCutStarGeometry G T S0 S1 (finiteStarCoreSet G T x y) x y loss:=by
  have hx:x∈S1:=hpair.symm ▸ Or.inl (center_mem_graphBall G x r)
  have hy:y∈S1:=hpair.symm ▸ Or.inr (center_mem_graphBall G y r)
  have hT:T⊆S1:=cut_neighborhood_captures_inner G T S1 hcap
  have htargets:=finiteStarCoreSet_targets G T x y
  refine ⟨?_,hsub,?_,hT.trans hsub,hT,?_,?_,?_,?_⟩
  · exact finiteStarCoreSet_subset G T S1 x y hx hy
      (fun t ht v htv=>hcap ⟨t,ht,(SimpleGraph.edist_eq_one_iff_adj.mpr htv).le⟩)
  · exact fun v hv=>finiteStarCoreSet_not_mem G T x y v hv
  · exact fun t ht v htv hv=>finiteStarCoreSet_neighbor G T x y t v ht htv hv
  · by_cases ht:x∈T
    · exact Or.inr ht
    · exact Or.inl (htargets.1 ht)
  · by_cases ht:y∈T
    · exact Or.inr ht
    · exact Or.inl (htargets.2 ht)
  · exact fun v hv=>hnear v (finiteStarCoreSet_subset_cut_region G T x y hv)

namespace LabelledResamplingState
variable {T:Set V}{ι:Type}[Fintype ι]

theorem full_pair_near_cut_star_geometry (s:LabelledResamplingState V T ι)
    (selector r:ℕ)(x y:V)(loss:ℕ)
    (hcap:graphSetBall (s.fullResample selector).graph T 1⊆pairBallVertices (s.fullResample selector).graph x y r)
    (hnear:∀v∈graphSetBall (s.fullResample selector).graph T 1∪{x,y},
      (s.fullResample selector).graph.edist x v≤(loss:ℕ∞) ∨
        (s.fullResample selector).graph.edist y v≤(loss:ℕ∞)):
    NearCutStarGeometry (s.fullResample selector).graph T (s.fullTwoTargetVertices selector r x y)
      (pairBallVertices (s.fullResample selector).graph x y r)
      (finiteStarCoreSet (s.fullResample selector).graph T x y) x y loss:=
  near_cut_star_geometry _ T _ _ x y r loss rfl
    (s.switched_full_pair_subset_old_augmentation selector r x y) hcap hnear

theorem full_pair_quarter_close_cut_star_geometry (s:LabelledResamplingState V T ι)
    (selector ell r:ℕ)(o x y:V)(hT:T=graphBallVertices s.graph o ell)
    (hroom:quarterCutLoss ell r≤r)
    (hclose:quarterCutClose (s.fullResample selector).graph T r x y):
    NearCutStarGeometry (s.fullResample selector).graph T (s.fullTwoTargetVertices selector r x y)
      (pairBallVertices (s.fullResample selector).graph x y r)
      (finiteStarCoreSet (s.fullResample selector).graph T x y) x y (quarterCutLoss ell r):=by
  rcases s.full_pair_quarter_cut_dichotomy selector ell r o x y hT hroom with hnear|hfar
  · exact s.full_pair_near_cut_star_geometry selector r x y _ hnear.2.1 hnear.2.2
  · obtain ⟨t,ht,hx|hy⟩:=hclose
    · exact False.elim (not_lt_of_ge hx (hfar.2.2 t ht).1)
    · exact False.elim (not_lt_of_ge hy (hfar.2.2 t ht).2)

end LabelledResamplingState
end LocalLaw
