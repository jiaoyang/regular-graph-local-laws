import LocalLaw.ResamplingBallPreservation
import LocalLaw.CavityAverage
import SpectralConsequences.BoundaryMeanAggregation

/-! The switched center has exactly its original neighbors, and its cavity
value is the genuine average of the corresponding singleton minors. -/
open scoped BigOperators
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance resampledRootNeighborsDecidable (p:Prop):Decidable p:=Classical.propDecidable p

namespace LabelledResamplingState
variable {V:Type} {T:Set V} {ι:Type} [Fintype ι]

theorem root_adjacency_preserved (s:LocalLaw.LabelledResamplingState V T ι)
    (o:V) (ell selector:ℕ) (hell:1≤ell)
    (hT:T=graphBallVertices s.graph o ell) (v:V):
    (s.fullResample selector).graph.Adj o v↔s.graph.Adj o v:=by
  have ho:o∈T:=hT.symm▸center_mem_graphBall s.graph o ell
  have hnew:graphBallVertices (s.fullResample selector).graph o ell=T:=by
    simpa only [graphSetBall_singleton] using
      s.fullResample_ball selector {o} ell (by simpa only [graphSetBall_singleton] using hT)
  have hmemold (ha:s.graph.Adj o v):v∈T:=by
    rw [hT]
    exact (SimpleGraph.edist_eq_one_iff_adj.mpr ha).le.trans (ENat.coe_le_coe.mpr hell)
  have hmemnew (ha:(s.fullResample selector).graph.Adj o v):v∈T:=by
    rw [←hnew]
    exact (SimpleGraph.edist_eq_one_iff_adj.mpr ha).le.trans (ENat.coe_le_coe.mpr hell)
  have hinside (hv:v∈T):
      (s.fullResample selector).graph.Adj o v↔s.graph.Adj o v:=by
    change ((s.fullResample selector).graph.induce T).Adj ⟨o,ho⟩ ⟨v,hv⟩↔
      (s.graph.induce T).Adj ⟨o,ho⟩ ⟨v,hv⟩
    rw [s.fullResample_induce selector]
  exact ⟨fun ha=>(hinside (hmemnew ha)).mp ha,fun ha=>(hinside (hmemold ha)).mpr ha⟩

end LabelledResamplingState

variable {V:Type*} [Fintype V] [DecidableEq V]

def neighborMinorValue (G:SimpleGraph V) (d:ℕ) (z:ℂ) (o:V) (j:G.neighborSet o):ℂ:=
  green (deletedMatrix (normalizedAdjacency G d) j.val) z
    ⟨o,j.property.ne⟩ ⟨o,j.property.ne⟩

theorem cavityAtVertex_neighbor_sum (G:SimpleGraph V) (d:ℕ) (z:ℂ) (o:V):
    cavityAtVertex G d z o=(d:ℂ)⁻¹*∑j:G.neighborSet o,neighborMinorValue G d z o j:=by
  unfold cavityAtVertex
  congr 1
  have hs:=Fintype.sum_subtype_add_sum_subtype (fun j:V=>G.Adj o j)
    (fun j=>orientedCavity G d z o j)
  have hzero:(∑j:{j:V//¬G.Adj o j},orientedCavity G d z o j.val)=0:=by
    apply Finset.sum_eq_zero
    intro j _
    simp only [orientedCavity]
    split_ifs with hne hadj
    · exact False.elim (j.property hadj)
    all_goals rfl
  rw [hzero,add_zero] at hs
  rw [←hs]
  apply Finset.sum_congr rfl
  intro j _
  simp only [orientedCavity,dif_pos j.property.ne,if_pos j.property,neighborMinorValue]

end SpectralConsequences
