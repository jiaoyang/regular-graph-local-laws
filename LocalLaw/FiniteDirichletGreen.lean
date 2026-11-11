import LocalLaw.GraphDirichletOperatorLimit
import LocalLaw.FiniteModel

/-! # A finite Dirichlet operator Green block is the actual finite matrix inverse -/

open scoped BigOperators Topology Matrix
noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
namespace LocalLaw
local instance finiteDirichletGreenDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*} [DecidableEq V]

def l2FiniteEmbedding (S : Finset V) (f : S → ℂ) : GraphL2 V := ∑ v : S,lp.single 2 v.val (f v)

theorem l2FiniteEmbedding_inside (S : Finset V) (f : S → ℂ) (v : S) : l2FiniteEmbedding S f v.val=f v := by
  change (∑ w : S,(lp.single 2 w.val (f w):GraphL2 V)) v.val=f v
  simp only [lp.coeFn_sum,Finset.sum_apply,lp.single_apply,Pi.single_apply]
  rw [Finset.sum_eq_single v]
  · simp
  · intro w _ hw
    exact if_neg (fun h => hw (Subtype.ext h.symm))
  · simp

theorem l2FiniteEmbedding_outside (S : Finset V) (f : S → ℂ) (v : V) (hv : v∉S) : l2FiniteEmbedding S f v=0 := by
  change (∑ w : S,(lp.single 2 w.val (f w):GraphL2 V)) v=0
  simp only [lp.coeFn_sum,Finset.sum_apply,lp.single_apply,Pi.single_apply]
  apply Finset.sum_eq_zero
  intro w _
  have hne : v≠w.val := fun h => hv (h.symm ▸ w.property)
  have hh : (Pi.single w.val (f w):V → ℂ) v=0 := Pi.single_eq_of_ne (f:=fun _ : V => ℂ) hne (f w)
  simpa only [Pi.single_apply] using hh

theorem l2FiniteEmbedding_basis (S : Finset V) (j : S) :
    l2FiniteEmbedding S (fun v => if v=j then (1:ℂ) else 0)=lp.single 2 j.val 1 := by
  unfold l2FiniteEmbedding
  rw [Finset.sum_eq_single j]
  · simp
  · intro v _ hv
    simp only [if_neg hv,lp.single_zero]
  · simp

end LocalLaw
open LocalLaw
namespace SimpleGraph
local instance finiteDirichletGreenRootDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [G.LocallyFinite]

theorem finiteDirichletRestriction_adjacency_embedding (S : Finset V) (D : ℕ) (hD : ∀ v,G.degree v≤D)
    (f : S → ℂ) :
    (G.finiteDirichletRestriction S).boundedAdjacency D
      (fun v => (G.finiteDirichletRestriction_degree_le S v).trans (hD v)) (l2FiniteEmbedding S f)=
      l2FiniteEmbedding S ((G.induce (S:Set V)).adjMatrix ℂ *ᵥ f) := by
  apply lp.ext
  funext v
  rw [boundedAdjacency_apply]
  by_cases hv : v∈S
  · let vs : S := ⟨v,hv⟩
    have hright := l2FiniteEmbedding_inside S ((G.induce (S:Set V)).adjMatrix ℂ *ᵥ f) vs
    change l2FiniteEmbedding S ((G.induce (S:Set V)).adjMatrix ℂ *ᵥ f) v=_ at hright
    rw [hright]
    simp only [l2FiniteEmbedding,lp.coeFn_sum,Finset.sum_apply,lp.single_apply,Pi.single_apply]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq',SimpleGraph.mem_neighborFinset,finiteDirichletRestriction,
      hv,true_and,Subtype.coe_prop,Matrix.mulVec,dotProduct,SimpleGraph.adjMatrix_apply,
      ite_mul,one_mul,zero_mul]
    apply Finset.sum_congr rfl
    intro w _
    change (if w.val∈S ∧ G.Adj v w.val then f w else 0)=(if G.Adj v w.val then f w else 0)
    simp only [w.property,true_and]
  · rw [G.finiteDirichletRestriction_neighborFinset,if_neg hv,Finset.sum_empty,
      l2FiniteEmbedding_outside S _ v hv]

theorem finiteDirichletRestriction_spectral_embedding (S : Finset V) (d : ℕ) (hD : ∀ v,G.degree v≤d)
    (z : ℂ) (f : S → ℂ) :
    (G.finiteDirichletRestriction S).graphSpectralOperator d
      (fun v => (G.finiteDirichletRestriction_degree_le S v).trans (hD v)) z (l2FiniteEmbedding S f)=
      l2FiniteEmbedding S (spectralMatrix (normalizedAdjacency (G.induce (S:Set V)) d) z *ᵥ f) := by
  have hA := G.finiteDirichletRestriction_adjacency_embedding S d hD f
  apply lp.ext
  funext v
  have hAv := congrFun (congrArg (fun u : GraphL2 V => (u : V → ℂ)) hA) v
  dsimp only at hAv
  simp only [graphSpectralOperator,normalizedOperator,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.one_apply,lp.coeFn_sub,lp.coeFn_smul,
    Pi.sub_apply,Pi.smul_apply]
  rw [hAv]
  by_cases hv : v∈S
  · let vs : S := ⟨v,hv⟩
    rw [show l2FiniteEmbedding S _ v=((G.induce (S:Set V)).adjMatrix ℂ *ᵥ f) vs from l2FiniteEmbedding_inside S _ vs,
      show l2FiniteEmbedding S f v=f vs from l2FiniteEmbedding_inside S f vs,
      show l2FiniteEmbedding S _ v=(spectralMatrix (normalizedAdjacency (G.induce (S:Set V)) d) z *ᵥ f) vs from
        l2FiniteEmbedding_inside S _ vs]
    simp only [spectralMatrix,normalizedAdjacency,Matrix.sub_mulVec,Matrix.smul_mulVec_assoc,Matrix.one_mulVec,
      Pi.sub_apply,Pi.smul_apply,Complex.real_smul,smul_eq_mul]
  · rw [l2FiniteEmbedding_outside S _ v hv,l2FiniteEmbedding_outside S _ v hv,l2FiniteEmbedding_outside S _ v hv]
    simp

theorem finiteDirichletRestriction_Green_eq_matrix (S : Finset V) (d : ℕ) (hD : ∀ v,G.degree v≤d)
    (z : ℂ) (hz : 0<z.im) (i j : S) :
    (G.finiteDirichletRestriction S).infiniteGreen d
      (fun v => (G.finiteDirichletRestriction_degree_le S v).trans (hD v)) z i.val j.val=
      green (normalizedAdjacency (G.induce (S:Set V)) d) z i j := by
  let H := normalizedAdjacency (G.induce (S:Set V)) d
  let R := green H z
  let f : S → ℂ := fun v => R v j
  let u := l2FiniteEmbedding S f
  have hinv := Matrix.mul_nonsing_inv (spectralMatrix H z)
    ((spectralMatrix H z).isUnit_iff_isUnit_det.mp (spectralMatrix_isUnit H (normalizedAdjacency_isHermitian _ _) z hz))
  have hfinite : spectralMatrix H z *ᵥ f=fun v => if v=j then 1 else 0 := by
    funext v
    exact congrFun (congrFun hinv v) j
  have hOp := G.finiteDirichletRestriction_spectral_embedding S d hD z f
  rw [hfinite,l2FiniteEmbedding_basis] at hOp
  let Q := (G.finiteDirichletRestriction S).infiniteGreenOperator d
    (fun v => (G.finiteDirichletRestriction_degree_le S v).trans (hD v)) z
  have hleft := (G.finiteDirichletRestriction S).infiniteGreenOperator_left_inverse d
    (fun v => (G.finiteDirichletRestriction_degree_le S v).trans (hD v)) z (ne_of_gt hz)
  have hsolve : Q (lp.single 2 j.val 1)=u := by
    rw [←hOp]
    exact congrArg (fun A : GraphL2 V →L[ℂ] GraphL2 V => A u) hleft
  change Q (lp.single 2 j.val 1) i.val=R i j
  rw [hsolve]
  exact l2FiniteEmbedding_inside S f i

end SimpleGraph
