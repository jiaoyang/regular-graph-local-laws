import LocalLaw.FiniteStarGeometry
import LocalLaw.FiniteStarTargets
import LocalLaw.SelectedFirstFullPairOccupancy
import LocalLaw.FullOutsideReplacement

/-! # Captured exterior sampled stars for arbitrary full-pair centers

Both regions are literal outside slices. An auxiliary outside replacement is
used only when applying old reference bounds, never to enlarge the first model.
-/

noncomputable section
set_option maxHeartbeats 1800000
namespace LocalLaw
local instance fullRegionStarLayoutDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace LabelledResamplingState
variable {V:Type} [Fintype V] [DecidableEq V] {T:Set V}{ι:Type}[Fintype ι]

def fullRegionInnerFirst (s:LabelledResamplingState V T ι)(selector r:ℕ)(x y:V) : Set (Tᶜ:Set V):=
  s.selectedFirstSet selector∩s.fullSliceOutside (pairBallVertices (s.fullResample selector).graph x y (r-2))

def fullRegionOuterFirst (s:LabelledResamplingState V T ι)(selector r:ℕ)(x y:V) : Set (Tᶜ:Set V):=
  s.selectedFirstSet selector\s.fullSliceOutside (pairBallVertices (s.fullResample selector).graph x y (r-2))

def fullRegionStarCore (s:LabelledResamplingState V T ι)(selector r:ℕ)(x y:V)(u v:(Tᶜ:Set V)) : Set (Tᶜ:Set V):=
  finiteStarCoreSet (outsideGraph (s.fullResample selector).graph T) (s.fullRegionInnerFirst selector r x y) u v\
    s.fullRegionOuterFirst selector r x y

omit [Fintype V] [DecidableEq V] in
theorem fullRegion_inner_outer_partition (s:LabelledResamplingState V T ι)(selector r:ℕ)(x y:V) :
    s.fullRegionInnerFirst selector r x y∪s.fullRegionOuterFirst selector r x y=s.selectedFirstSet selector:=by
  ext v
  simp only[fullRegionInnerFirst,fullRegionOuterFirst,Set.mem_union,Set.mem_inter_iff,Set.mem_diff]
  tauto

omit [Fintype V] [DecidableEq V] in
theorem fullRegion_inner_not_outer (s:LabelledResamplingState V T ι)(selector r:ℕ)(x y:V) :
    ∀v∈s.fullRegionInnerFirst selector r x y,v∉s.fullRegionOuterFirst selector r x y:=by
  intro v hv ho
  exact ho.2 hv.2

omit [DecidableEq V] in
theorem fullRegionInnerFirst_card (s:LabelledResamplingState V T ι)(selector r:ℕ)(x y:V)
    (hsep:2*(r-2)≤selector) : Nat.card (s.fullRegionInnerFirst selector r x y)≤2:=by
  let S:=s.fullSliceOutside (pairBallVertices (s.fullResample selector).graph x y (r-2))
  have he:=s.partialFirstRemovalInterEquiv selector S
  change Nat.card {v:(Tᶜ:Set V)//v∈s.selectedFirstSet selector ∧ v∈S}≤2
  rw[←Nat.card_congr he]
  exact s.partialFirstRemovedSet_new_full_pair_card selector (r-2) hsep x y

omit [Fintype V] [DecidableEq V] in
theorem fullRegion_inner_pair_capture (s:LabelledResamplingState V T ι)(selector r:ℕ)(x y:V) :
    s.fullRegionInnerFirst selector r x y⊆s.fullSliceOutside (pairBallVertices (s.fullResample selector).graph x y r):=by
  intro b hb
  rcases hb.2 with hx|hy
  · exact Or.inl (hx.trans (ENat.coe_le_coe.mpr (Nat.sub_le r 2)))
  · exact Or.inr (hy.trans (ENat.coe_le_coe.mpr (Nat.sub_le r 2)))

omit [Fintype V] [DecidableEq V] in
theorem fullRegion_inner_neighbors_captured (s:LabelledResamplingState V T ι)(selector r:ℕ)(hr:1≤r)(x y:V)
    (b v:(Tᶜ:Set V))(hb:b∈s.fullRegionInnerFirst selector r x y)
    (hadj:(outsideGraph (s.fullResample selector).graph T).Adj b v) :
    v∈s.fullSliceOutside (pairBallVertices (s.fullResample selector).graph x y r):=by
  let G:=(s.fullResample selector).graph
  have he:G.edist b.val v.val=1:=SimpleGraph.edist_eq_one_iff_adj.mpr hadj
  have hroom:(r-2)+1≤r:=by omega
  have hone (a:V)(ha:G.edist a b.val≤((r-2:ℕ):ℕ∞)):G.edist a v.val≤(r:ℕ∞):=by
    calc
      _≤G.edist a b.val+G.edist b.val v.val:=G.edist_triangle
      _≤((r-2:ℕ):ℕ∞)+1:=by rw[he];exact add_le_add_right ha _
      _≤(r:ℕ∞):=by exact_mod_cast hroom
  rcases hb.2 with hx|hy
  · exact Or.inl (hone x hx)
  · exact Or.inr (hone y hy)

omit [Fintype V] [DecidableEq V] [Fintype ι] in
theorem selectedFirstSet_subset_fullRegion (s:LabelledResamplingState V T ι)(selector r:ℕ)(x y:V) :
    s.selectedFirstSet selector⊆s.fullSliceOutside (s.fullTwoTargetVertices selector r x y):=by
  rintro b ⟨i,rfl⟩
  apply Or.inl
  apply Or.inr
  refine ⟨s.admissibleSampleVertex selector i,?_,rfl⟩
  exact ⟨s.admissibleSampleVertex selector i,Or.inr (Set.mem_iUnion.mpr ⟨i,Or.inl rfl⟩),by
    change (outsideGraph s.graph T).edist (s.admissibleSampleVertex selector i)
      (s.admissibleSampleVertex selector i)≤(r:ℕ∞)
    rw[SimpleGraph.edist_self]
    exact bot_le⟩

theorem fullRegionStarLayout (s:LabelledResamplingState V T ι)(selector r:ℕ)(hr:1≤r)(x y:V)(u v:(Tᶜ:Set V))
    (hu:u∈s.fullSliceOutside (pairBallVertices (s.fullResample selector).graph x y r))
    (hv:v∈s.fullSliceOutside (pairBallVertices (s.fullResample selector).graph x y r)) :
    CapturedStarLayout (outsideGraph (s.fullResample selector).graph T)
      (s.fullSliceOutside (s.fullTwoTargetVertices selector r x y))
      (s.fullSliceOutside (pairBallVertices (s.fullResample selector).graph x y r))
      (s.fullRegionOuterFirst selector r x y) (s.fullRegionStarCore selector r x y u v)
      (s.fullRegionInnerFirst selector r x y):=by
  have hS:s.fullSliceOutside (pairBallVertices (s.fullResample selector).graph x y r)⊆
      s.fullSliceOutside (s.fullTwoTargetVertices selector r x y):=fun _ h=>s.switched_full_pair_subset_old_augmentation selector r x y h
  have hJ:=s.fullRegion_inner_pair_capture selector r x y
  have hI:finiteStarCoreSet (outsideGraph (s.fullResample selector).graph T)
      (s.fullRegionInnerFirst selector r x y) u v⊆
      s.fullSliceOutside (pairBallVertices (s.fullResample selector).graph x y r):=by
    apply finiteStarCoreSet_subset _ _ _ _ _ hu hv
    exact fun b hb v hv=>s.fullRegion_inner_neighbors_captured selector r hr x y b v hb hv
  refine ⟨fun _ h=>hS (hI h.1),fun _ h=>hI h.1,fun _ h=>hS (hJ h),hJ,
    fun _ h=>h.2,s.fullRegion_inner_not_outer selector r x y,?_,?_,?_,?_⟩
  · intro z hz
    exact finiteStarCoreSet_not_mem _ _ u v z hz.1
  · intro b hb z hz
    exact hS (s.fullRegion_inner_neighbors_captured selector r hr x y b z hb hz)
  · exact fun b hb v hv=>s.fullRegion_inner_neighbors_captured selector r hr x y b v hb hv
  · intro b hb z hz ho hj
    exact ⟨finiteStarCoreSet_neighbor _ _ u v b z hb hz hj,ho⟩

theorem fullRegionStarCore_targets (s:LabelledResamplingState V T ι)(selector r:ℕ)(x y:V)(u v:(Tᶜ:Set V))
    (hu:u∉s.fullRegionOuterFirst selector r x y)(hv:v∉s.fullRegionOuterFirst selector r x y) :
    (u∈s.fullRegionStarCore selector r x y u v∨u∈s.fullRegionInnerFirst selector r x y) ∧
    (v∈s.fullRegionStarCore selector r x y u v∨v∈s.fullRegionInnerFirst selector r x y):=by
  have ht:=finiteStarCoreSet_targets (outsideGraph (s.fullResample selector).graph T)
    (s.fullRegionInnerFirst selector r x y) u v
  constructor
  · by_cases h:u∈s.fullRegionInnerFirst selector r x y
    · exact Or.inr h
    · exact Or.inl ⟨ht.1 h,hu⟩
  · by_cases h:v∈s.fullRegionInnerFirst selector r x y
    · exact Or.inr h
    · exact Or.inl ⟨ht.2 h,hv⟩

theorem fullRegionStarIndex_card (s:LabelledResamplingState V T ι)(selector r d:ℕ)(hd:1≤d)(x y:V)
    (u v:(Tᶜ:Set V))(hsep:2*(r-2)≤selector)
    (hdegree:∀w,(outsideGraph (s.fullResample selector).graph T).degree w≤d) :
    Nat.card (s.fullRegionStarCore selector r x y u v⊕s.fullRegionInnerFirst selector r x y)≤4*d+2:=by
  have hI:Nat.card (s.fullRegionStarCore selector r x y u v)≤
      Nat.card (finiteStarCoreSet (outsideGraph (s.fullResample selector).graph T)
        (s.fullRegionInnerFirst selector r x y) u v):=
    Nat.card_le_card_of_injective (fun z=>⟨z.val,z.property.1⟩)
      (fun _ _ h=>Subtype.ext (congrArg
        (fun z:finiteStarCoreSet (outsideGraph (s.fullResample selector).graph T) (s.fullRegionInnerFirst selector r x y) u v=>z.val) h))
  have hh:=finiteStarIndex_card_four _ _ u v d hd hdegree (s.fullRegionInnerFirst_card selector r x y hsep)
  rw[Nat.card_sum] at hh ⊢
  omega

end LabelledResamplingState
end LocalLaw
