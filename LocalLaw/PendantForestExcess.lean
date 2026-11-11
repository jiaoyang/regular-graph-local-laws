import LocalLaw.EvenCutsets
import LocalLaw.DisconnectedEvenTransfer

/-! # Pendant forests cannot increase the actual finite excess

The retained set may be disconnected. Every actual outside component is a
tree with at most one cut edge; hence an even edge pattern is supported in
the retained set. This supplies a componentwise excess comparison.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
set_option maxHeartbeats 1800000
local instance pendantForestExcessDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*} [Fintype V]

 theorem even_pattern_supported_core_of_pendant_forest (G : SimpleGraph V) (S : Set V)
    (htree : ∀ C : CutComponent G S, (cutComponentGraph G S C).IsAcyclic)
    (hcut : ∀ C : CutComponent G S, cutMultiplicity G S C ≤ 1)
    (F : EvenEdgeSubgraph G) : F.val.support ⊆ S := by
  intro x hx
  by_contra hxS
  let xx : (Sᶜ : Set V) := ⟨x,hxS⟩
  let C : CutComponent F.val S := (outsideGraph F.val S).connectedComponentMk xx
  let D : CutComponent G S := (outsideGraph G S).connectedComponentMk xx
  let f : outsideGraph F.val S →g outsideGraph G S :=
    { toFun := id, map_rel' := fun h => F.property.1 h }
  have hD (y : C.supp) : y.val ∈ D.supp := by
    exact SimpleGraph.ConnectedComponent.sound
      ((SimpleGraph.ConnectedComponent.exact y.property).map f)
  let inc : cutComponentGraph F.val S C →g cutComponentGraph G S D :=
    { toFun := fun y => ⟨y.val,hD y⟩, map_rel' := fun h => F.property.1 h }
  have hinj : Function.Injective inc := by
    intro y z h
    exact Subtype.ext (congrArg (fun w : D.supp => w.val) h)
  let boundary : CutBoundaryEdge F.val S C → CutBoundaryEdge G S D := fun e =>
    ⟨⟨e.val.val,F.property.1 e.val.property.1,e.val.property.2⟩,hD ⟨_,e.property⟩⟩
  have hbinj : Function.Injective boundary := by
    intro e g h
    exact Subtype.ext (Subtype.ext (congrArg (fun w : CutBoundaryEdge G S D => w.val.val) h))
  have hcutF : cutMultiplicity F.val S C ≤ 1 :=
    (Nat.card_le_card_of_injective boundary hbinj).trans (hcut D)
  have hzero := cutMultiplicity_eq_zero_of_even_le_one F.val S F.property.2 C hcutF
  have hdefzero (y : C.supp) : cutDeficit F.val S C y = 0 := by
    have hsum := cutMultiplicity_eq_sum_deficit F.val S C
    have hle : cutDeficit F.val S C y ≤ ∑ z : C.supp, cutDeficit F.val S C z :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ y)
    rw [hzero] at hsum
    simp only [← finsum_eq_sum_of_fintype] at hsum hle
    omega
  have hforest : (cutComponentGraph F.val S C).IsAcyclic := by
    intro v p hp
    exact htree D (p.map inc) (hp.map hinj)
  have heven : ∀ y : C.supp, Even ((cutComponentGraph F.val S C).degree y) := by
    intro y
    have hh := cutComponent_ambient_degree_identity F.val S C y
    rw [hdefzero y,Nat.add_zero] at hh
    have he := F.property.2 y.val.val
    simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hh he ⊢
    rwa [← hh]
  have hempty := even_forest_eq_bot _ hforest heven
  let y : C.supp := ⟨xx,rfl⟩
  have hdegree := cutComponent_ambient_degree_identity F.val S C y
  rw [hempty,hdefzero y] at hdegree
  have hpos : 0 < F.val.degree x := (F.val.degree_pos_iff_mem_support x).mpr hx
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hdegree hpos
  have hbot : Nat.card ((⊥ : SimpleGraph C.supp).neighborSet y) = 0 := by simp
  rw [hbot,Nat.zero_add] at hdegree
  have hdegreeX : Nat.card (F.val.neighborSet x) = 0 := hdegree
  omega

 theorem pendant_forest_connected_embedding_excess_le {U : Type*} [Fintype U]
    (B : SimpleGraph U) (G H : SimpleGraph V) (S : Set V) (emb : U ↪ V)
    (hB : B.Connected) (hBG : ∀ {x y}, B.Adj x y → G.Adj (emb x) (emb y))
    (htree : ∀ C : CutComponent G S, (cutComponentGraph G S C).IsAcyclic)
    (hcut : ∀ C : CutComponent G S, cutMultiplicity G S C ≤ 1)
    (hcore : ∀ {x y}, x ∈ S → y ∈ S → G.Adj x y → H.Adj x y) :
    graphExcess B ≤ graphExcess (H.induce S) := by
  apply graphExcess_le_of_even_pattern_localization_general B H emb S hB
  · intro F x y hxy
    have hmapped : F.val.map emb ≤ G := by
      rintro a b ⟨u,v,huv,hab⟩
      simpa only [hab.1,hab.2] using hBG (F.property.1 huv)
    have heven := mapped_even_pattern F.val emb F.property.2
    let E : EvenEdgeSubgraph G := ⟨F.val.map emb,hmapped,by
      intro v
      have hh := heven v
      simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hh ⊢
      exact hh⟩
    have hs := even_pattern_supported_core_of_pendant_forest G S htree hcut E
    exact hcore (hs ((E.val.mem_support).mpr ⟨y,hxy⟩))
      (hs ((E.val.mem_support).mpr ⟨x,hxy.symm⟩)) (hmapped hxy)
  · intro F
    have hmapped : F.val.map emb ≤ G := by
      rintro a b ⟨u,v,huv,hab⟩
      simpa only [hab.1,hab.2] using hBG (F.property.1 huv)
    exact even_pattern_supported_core_of_pendant_forest G S htree hcut
      ⟨F.val.map emb,hmapped,by
        intro v
        have hh := mapped_even_pattern F.val emb F.property.2 v
        simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hh ⊢
        exact hh⟩

end LocalLaw
