import LocalLaw.EvenCutsets
import LocalLaw.ResamplingTripleGeometry
import LocalLaw.ShortCyclePatterns

/-!
# Small even patterns avoid accepted resampling triples

An even edge pattern on at most radius+1 supported vertices cannot meet an
accepted exterior triple. In its outside component, short paths and J force
every attachment to use the same boundary label. Cut parity then forces zero
attachments. The I-tree makes that component acyclic, so evenness forces it
empty, contradicting the supported vertex. This is an actual geometric
exclusion theorem, not a hypothesis about switched cycles.
-/

noncomputable section
set_option maxHeartbeats 1800000
namespace LocalLaw

local instance resamplingEvenPatternDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*} [Fintype V]

omit [Fintype V] in
theorem outside_component_supported (F : SimpleGraph V) (T : Set V)
    (C : CutComponent F T) (x : C.supp) (hx : x.val.val ∈ F.support) :
    ∀ y : C.supp, y.val.val ∈ F.support := by
  intro y
  obtain ⟨p⟩ := C.connected_induce_supp y x
  cases p with
  | nil => exact hx
  | @cons y u x h p => exact (F.mem_support).mpr ⟨u.val.val, h⟩

theorem outside_component_card_le_support (F : SimpleGraph V) (T : Set V)
    (C : CutComponent F T) (x : C.supp) (hx : x.val.val ∈ F.support) :
    Nat.card C.supp ≤ F.support.toFinset.card := by
  let f : C.supp → F.support := fun y => ⟨y.val.val, outside_component_supported F T C x hx y⟩
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : F.support => z.val) h
  have h := Nat.card_le_card_of_injective f hf
  simpa only [Set.toFinset_card, ← Nat.card_eq_fintype_card] using h

namespace LabelledResamplingState
variable {T : Set V} {ι : Type*}

/-- Every even edge pattern on at most radius+1 supported vertices avoids
each actually eligible triple. In particular this applies to simple cycles. -/
theorem eligible_even_pattern_avoids_triple (s : LabelledResamplingState V T ι)
    (radius : ℕ) (i : ι) (hi : s.Eligible radius i)
    (F : SimpleGraph V) (hFG : F ≤ s.graph) (heven : ∀ v, Even (F.degree v))
    (hsize : F.support.toFinset.card ≤ radius + 1) :
    ∀ x ∈ s.triple i, x.val ∉ F.support := by
  intro x hx hxF
  let C : CutComponent F T := (outsideGraph F T).connectedComponentMk x
  let xx : C.supp := ⟨x, rfl⟩
  have hcard : Nat.card C.supp ≤ radius + 1 :=
    (outside_component_card_le_support F T C xx hxF).trans hsize
  have hpath : ∀ y : C.supp, (outsideGraph s.graph T).edist x y.val ≤ (radius : ℕ∞) := by
    intro y
    obtain ⟨p, hp⟩ := C.connected_induce_supp.exists_isPath xx y
    have hlen := hp.length_lt
    have hcard' : Fintype.card C.supp ≤ radius + 1 := by
      simpa only [Nat.card_eq_fintype_card] using hcard
    have hle : p.length ≤ radius := by omega
    let f : cutComponentGraph F T C →g outsideGraph s.graph T :=
      { toFun := fun v => v.val
        map_rel' := fun h => hFG h }
    exact ((outsideGraph s.graph T).edist_le (p.map f)).trans
      (by simpa only [SimpleGraph.Walk.length_map] using ENat.coe_le_coe.mpr hle)
  let bmap : CutBoundaryEdge F T C → BoundaryOrientedEdge s.graph T := fun e =>
    ⟨e.val.val, hFG e.val.property.1, e.val.property.2⟩
  have hboundary : ∀ e : CutBoundaryEdge F T C, bmap e = s.boundary i := by
    intro e
    by_contra hne
    let y : C.supp := ⟨⟨e.val.val.2, e.val.property.2.2⟩, e.property⟩
    have hy : y.val ∈ outsideTriple s.graph T s.samples (bmap e) := by
      simp only [outsideTriple, sampledSwitchingQuad, SwitchingQuad.exterior,
        Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      exact Or.inl rfl
    have hfar := hi.2 (bmap e) hne x hx y.val hy
    exact (not_lt_of_ge (hpath y)) hfar
  have hcutle : cutMultiplicity F T C ≤ 1 := by
    let f : CutBoundaryEdge F T C → Unit := fun _ => ()
    have hf : Function.Injective f := by
      intro e f _
      have hb : bmap e = bmap f := (hboundary e).trans (hboundary f).symm
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : BoundaryOrientedEdge s.graph T => z.val) hb
    simpa only [cutMultiplicity, Nat.card_eq_fintype_card, Fintype.card_unit] using
      Nat.card_le_card_of_injective f hf
  have hcutzero : cutMultiplicity F T C = 0 :=
    cutMultiplicity_eq_zero_of_even_le_one F T heven C hcutle
  have hdefzero : ∀ y : C.supp, cutDeficit F T C y = 0 := by
    intro y
    have hsum := cutMultiplicity_eq_sum_deficit F T C
    have hle : cutDeficit F T C y ≤ ∑ v : C.supp, cutDeficit F T C v :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ y)
    omega
  have hforest : (cutComponentGraph F T C).IsAcyclic := by
    have hI := hi.1.tree.IsAcyclic
    let f : cutComponentGraph F T C →g
        ((outsideGraph s.graph T ⊔ SimpleGraph.edge
          (boundaryOutsideVertex s.graph T (s.boundary i))
          (sampledFirstOutsideVertex s.graph T s.samples (s.boundary i))).induce
          (s.tripleBall radius i)) :=
      { toFun := fun y => ⟨y.val, x, hx, hpath y⟩
        map_rel' := fun h => Or.inl (hFG h) }
    have hf : Function.Injective f := by
      intro a b h
      apply Subtype.ext
      exact congrArg (fun z : s.tripleBall radius i => z.val) h
    intro y p hp
    exact hI (p.map f) (hp.map hf)
  have hcomponentEven : ∀ y : C.supp, Even ((cutComponentGraph F T C).degree y) := by
    intro y
    have h := cutComponent_ambient_degree_identity F T C y
    rw [hdefzero y, Nat.add_zero] at h
    exact h ▸ heven y.val.val
  have hempty := even_forest_eq_bot (cutComponentGraph F T C) hforest hcomponentEven
  have hdegree := cutComponent_ambient_degree_identity F T C xx
  rw [hempty, hdefzero xx] at hdegree
  have hxpos : 0 < F.degree x.val := (F.degree_pos_iff_mem_support x.val).mpr hxF
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hdegree hxpos
  have hbot : Nat.card ((⊥ : SimpleGraph C.supp).neighborSet xx) = 0 := by simp
  rw [hbot, Nat.zero_add] at hdegree
  have hzero : Nat.card (F.neighborSet x.val) = 0 := hdegree
  omega

variable [Fintype ι]

/-- The same exclusion applies to the actual final graph and the original
accepted label, because the actual selector is invariant. -/
theorem fullResample_even_pattern_avoids_triple (s : LabelledResamplingState V T ι)
    (radius : ℕ) (i : ι) (hi : s.Eligible radius i)
    (F : SimpleGraph V) (hFG : F ≤ (s.fullResample radius).graph)
    (heven : ∀ v, Even (F.degree v)) (hsize : F.support.toFinset.card ≤ radius + 1) :
    ∀ x ∈ s.triple i, x.val ∉ F.support := by
  have h := (s.fullResample radius).eligible_even_pattern_avoids_triple radius i
    ((s.fullResample_eligible radius i).mpr hi) F hFG heven hsize
  rwa [s.fullResample_triple radius i] at h

end LabelledResamplingState
end LocalLaw
