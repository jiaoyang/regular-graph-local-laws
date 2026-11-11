import SpectralConsequences.ResampledRootNeighbors
import SpectralConsequences.SourceCavityPhysicalDrift

/-! Exact passage from deleted-neighbor drifts to the center cavity observable. -/
open scoped BigOperators
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance cavityVertexMeanDecidable (p:Prop):Decidable p:=Classical.propDecidable p
variable {V:Type*} [Fintype V] [DecidableEq V]

def neighborSetCongr (G H:SimpleGraph V) (o:V) (he:∀v,H.Adj o v↔G.Adj o v):
    G.neighborSet o≃H.neighborSet o where
  toFun j:=⟨j.val,(he j.val).mpr j.property⟩
  invFun j:=⟨j.val,(he j.val).mp j.property⟩
  left_inv _:=rfl
  right_inv _:=rfl

def rootNeighborInBall (G:SimpleGraph V) (o:V) (ell:ℕ) (hell:1≤ell)
    (j:G.neighborSet o):graphBallVertices G o ell:=
  ⟨j.val,(SimpleGraph.edist_eq_one_iff_adj.mpr j.property).le.trans (ENat.coe_le_coe.mpr hell)⟩

theorem cavityAtVertex_old_neighbor_sum (G H:SimpleGraph V) (d:ℕ) (z:ℂ) (o:V)
    (he:∀v,H.Adj o v↔G.Adj o v):
    cavityAtVertex H d z o=(d:ℂ)⁻¹*∑j:G.neighborSet o,
      green (deletedMatrix (normalizedAdjacency H d) j.val) z
        ⟨o,j.property.ne⟩ ⟨o,j.property.ne⟩:=by
  rw [cavityAtVertex_neighbor_sum H d z o]
  congr 1
  exact (Fintype.sum_equiv (neighborSetCongr G H o he)
    (fun j=>green (deletedMatrix (normalizedAdjacency H d) j.val) z ⟨o,j.property.ne⟩ ⟨o,j.property.ne⟩)
    (neighborMinorValue H d z o) (fun _=>rfl)).symm

theorem finiteComplexMean_comm {E J:Type*} [Fintype E] [Fintype J] (f:E→J→ℂ):
    finiteComplexMean (fun e=>finiteComplexMean (f e))=
      finiteComplexMean (fun j=>finiteComplexMean (fun e=>f e j)):=by
  unfold finiteComplexMean
  simp only [Complex.real_smul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro e _
  ring

namespace RegularGraph
variable {N d:ℕ}

theorem resampled_cavityAtVertex_eq_neighbor_mean (g:LocalLaw.RegularGraph N d)
    (o:Fin N) (ell:ℕ) (hell:1≤ell)
    {ι:Type}[Fintype ι]
    (labels:ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o ell))
    (samples:LocalSamplingFiber g.graph (graphBallVertices g.graph o ell)) (selector:ℕ) (z:ℂ):
    let T:=graphBallVertices g.graph o ell
    let new:=g.labelledResampledGraph T labels samples selector
    cavityAtVertex new.graph d z o=finiteComplexMean (fun j:g.graph.neighborSet o=>
      let jt:=rootNeighborInBall g.graph o ell hell j
      new.retainedPhysicalMinor T jt z (g.truncatedCavityRoot o ell jt j.property.symm)
        (g.truncatedCavityRoot o ell jt j.property.symm)):=by
  let T:=graphBallVertices g.graph o ell
  let s:=g.admissibleState T labels samples
  let new:=g.labelledResampledGraph T labels samples selector
  have he:∀v,new.graph.Adj o v↔g.graph.Adj o v:=
    SpectralConsequences.LabelledResamplingState.root_adjacency_preserved s o ell selector hell rfl
  have hh:=cavityAtVertex_old_neighbor_sum g.graph new.graph d z o he
  have hc:Fintype.card (g.graph.neighborSet o)=d:=by
    rw [SimpleGraph.card_neighborSet_eq_degree]
    exact g.regular o
  dsimp only
  rw [hh]
  unfold finiteComplexMean
  simp only [Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_natCast,hc]
  congr 1

end RegularGraph
end SpectralConsequences
