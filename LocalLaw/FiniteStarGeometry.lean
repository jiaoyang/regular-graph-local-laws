import LocalLaw.CapturedStarReduction
import LocalLaw.InnerSelectedGeometry

/-! # A bounded core for captured finite stars

The core contains the targets not in the sampled set and every nonsampled
neighbor of a sampled vertex. Its size is at most 2+|J|d.
-/

noncomputable section
namespace LocalLaw
local instance finiteStarGeometryDecidable (p:Prop):Decidable p:=Classical.propDecidable p
variable {V:Type} [Fintype V] [DecidableEq V]

def finiteStarCoreFinset (G:SimpleGraph V) (J:Set V) (x y:V) : Finset V :=
  (({x,y}:Finset V) ∪ J.toFinset.biUnion (fun b=>G.neighborFinset b)).filter (fun v=>v∉J)

def finiteStarCoreSet (G:SimpleGraph V) (J:Set V) (x y:V) : Set V :=
  {v |v∈finiteStarCoreFinset G J x y}

theorem finiteStarCoreSet_not_mem (G:SimpleGraph V)(J:Set V)(x y v:V)
    (hv:v∈finiteStarCoreSet G J x y) : v∉J := (Finset.mem_filter.mp hv).2

theorem finiteStarCoreSet_neighbor (G:SimpleGraph V)(J:Set V)(x y b v:V)
    (hb:b∈J)(hadj:G.Adj b v)(hv:v∉J) : v∈finiteStarCoreSet G J x y := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_union.mpr (Or.inr ?_),hv⟩
  exact Finset.mem_biUnion.mpr ⟨b,Set.mem_toFinset.mpr hb,by simpa using hadj⟩

theorem finiteStarCoreSet_targets (G:SimpleGraph V)(J:Set V)(x y:V) :
    (x∉J→x∈finiteStarCoreSet G J x y) ∧ (y∉J→y∈finiteStarCoreSet G J x y) := by
  constructor <;> intro h <;> apply Finset.mem_filter.mpr
  · exact ⟨Finset.mem_union.mpr (Or.inl (by simp)),h⟩
  · exact ⟨Finset.mem_union.mpr (Or.inl (by simp)),h⟩

theorem finiteStarCoreSet_subset (G:SimpleGraph V)(J S:Set V)(x y:V)
    (hx:x∈S)(hy:y∈S)(hcap:∀b∈J,∀v,G.Adj b v→v∈S) :
    finiteStarCoreSet G J x y⊆S := by
  intro v hv
  rcases Finset.mem_union.mp (Finset.mem_filter.mp hv).1 with h|h
  · rcases (show v=x ∨ v=y by simpa only [Finset.mem_insert,Finset.mem_singleton] using h) with h|h
    · exact h ▸ hx
    · exact h ▸ hy
  · rcases Finset.mem_biUnion.mp h with ⟨b,hb,hv⟩
    exact hcap b (Set.mem_toFinset.mp hb) v (by simpa using hv)

theorem finiteStarCoreSet_card (G:SimpleGraph V)(J:Set V)(x y:V)(d:ℕ)
    (hdegree:∀v,G.degree v≤d) :
    Nat.card (finiteStarCoreSet G J x y)≤2+Nat.card J*d := by
  have hbi : (J.toFinset.biUnion (fun b=>G.neighborFinset b)).card≤J.toFinset.card*d :=
    Finset.card_biUnion_le_card_mul _ _ _ (fun b _=>by simpa using hdegree b)
  have hp : ({x,y}:Finset V).card≤2 := by
    have hh:=Finset.card_insert_le x ({y}:Finset V)
    simpa using hh
  have hc := (Finset.card_filter_le (({x,y}:Finset V) ∪ J.toFinset.biUnion (fun b=>G.neighborFinset b))
    (fun v=>v∉J)).trans (Finset.card_union_le _ _)
  have hset : Nat.card (finiteStarCoreSet G J x y)=(finiteStarCoreFinset G J x y).card := by
    simp [finiteStarCoreSet,Nat.card_eq_fintype_card]
  rw [hset]
  dsimp only [finiteStarCoreFinset]
  have hj : J.toFinset.card=Nat.card J := by simp [Nat.card_eq_fintype_card]
  rw [←hj]
  omega

theorem finiteStarIndex_card (G:SimpleGraph V)(J:Set V)(x y:V)(d:ℕ)
    (hdegree:∀v,G.degree v≤d)(hJ:Nat.card J≤2) :
    Nat.card (finiteStarCoreSet G J x y⊕J)≤2*d+4 := by
  rw [Nat.card_sum]
  have h:=finiteStarCoreSet_card G J x y d hdegree
  nlinarith

theorem finiteStarIndex_card_four (G:SimpleGraph V)(J:Set V)(x y:V)(d:ℕ)
    (hd:1≤d)(hdegree:∀v,G.degree v≤d)(hJ:Nat.card J≤2) :
    Nat.card (finiteStarCoreSet G J x y⊕J)≤4*d+2 := by
  have h:=finiteStarIndex_card G J x y d hdegree hJ
  omega

end LocalLaw
