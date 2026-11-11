import LocalLaw.CoreAttachments

/-!
# An actual tree path adds a single fresh graft tail

A connected induced subtree contains the entire root path to each of its
vertices. The last old vertex of any new root path therefore splits it into
an old prefix and a simple tail whose remaining vertices are all fresh.
-/

namespace LocalLaw
noncomputable section
local instance treeGraftDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*} [DecidableEq V] {T : SimpleGraph V}

omit [DecidableEq V] in
/-- Unique tree paths make every connected induced subtree path-convex. -/
theorem subtree_root_path_support (hT : T.IsAcyclic) (S : Set V) (hS : (T.induce S).Connected)
    (root v : V) (hr : root ∈ S) (hv : v ∈ S) (p : T.Walk root v) (hp : p.IsPath) :
    ∀ x ∈ p.support, x ∈ S := by
  obtain ⟨q, hq⟩ := hS.exists_isPath (⟨root, hr⟩ : S) (⟨v, hv⟩ : S)
  let e := (SimpleGraph.Embedding.induce (G := T) S).toHom
  have hqmap : (q.map e).IsPath := SimpleGraph.Walk.map_isPath_of_injective Subtype.val_injective hq
  have heq : p = q.map e := congrArg Subtype.val (hT.path_unique ⟨p, hp⟩ ⟨q.map e, hqmap⟩)
  intro x hx
  rw [heq, SimpleGraph.Walk.support_map] at hx
  obtain ⟨y, _, hxy⟩ := List.mem_map.mp hx
  exact hxy ▸ y.property

/-- In a simple path, the first visit to a given indexed vertex is exactly
that index. This justifies the selected graft position. -/
theorem path_takeUntil_index {root v : V} (p : T.Walk root v) (hp : p.IsPath)
    (a : ℕ) (ha : a ≤ p.length) :
    (p.takeUntil (p.getVert a) (p.getVert_mem_support a)).length = a := by
  let w := p.getVert a
  let hw := p.getVert_mem_support a
  have hlen := p.length_takeUntil_le hw
  have heq : p.getVert (p.takeUntil w hw).length = p.getVert a := by
    rw [← SimpleGraph.Walk.getVert_takeUntil hw (le_refl _), SimpleGraph.Walk.getVert_length]
  exact hp.getVert_injOn hlen ha heq

/-- The suffix beyond the last old vertex is fresh off the old subtree. -/
theorem tree_path_graft_tail (hT : T.IsAcyclic) (S : Set V) (hS : (T.induce S).Connected)
    (root v : V) (hr : root ∈ S) (p : T.Walk root v) (hp : p.IsPath) :
    ∃ (w : V) (hw : w ∈ p.support),
      w ∈ S ∧
      (∀ x ∈ (p.takeUntil w hw).support, x ∈ S) ∧
      (∀ x ∈ (p.dropUntil w hw).support, x ≠ w → x ∉ S) ∧
      (p.dropUntil w hw).IsPath ∧ (p.dropUntil w hw).length ≤ p.length := by
  classical
  let old : Finset ℕ := (Finset.range (p.length + 1)).filter (fun a => p.getVert a ∈ S)
  have hzero : 0 ∈ old := by simp [old, p.getVert_zero, hr]
  have hnonempty : old.Nonempty := ⟨0, hzero⟩
  let a := old.max' hnonempty
  have hamem : a ∈ old := Finset.max'_mem old hnonempty
  obtain ⟨haRange, haS⟩ := Finset.mem_filter.mp hamem
  have ha : a ≤ p.length := by have hh := Finset.mem_range.mp haRange; omega
  let w := p.getVert a
  let hw := p.getVert_mem_support a
  have hwS : w ∈ S := haS
  let q := p.takeUntil w hw
  let r := p.dropUntil w hw
  have hq : q.IsPath := hp.takeUntil hw
  have hqS : ∀ x ∈ q.support, x ∈ S := subtree_root_path_support hT S hS root w hr hwS q hq
  have hqLength : q.length = a := path_takeUntil_index p hp a ha
  have hsplit : q.append r = p := p.take_spec hw
  have hdisjoint : List.Disjoint q.support r.support.tail := by
    apply List.disjoint_of_nodup_append
    rw [← SimpleGraph.Walk.support_append, hsplit]
    exact hp.support_nodup
  refine ⟨w, hw, hwS, hqS, ?_, hp.dropUntil hw, p.length_dropUntil_le hw⟩
  intro x hx hxw hxS
  have hxWhole : x ∈ p.support := p.support_dropUntil_subset hw hx
  obtain ⟨k, hkx, hk⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hxWhole
  have hkOld : k ∈ old := Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (by omega), hkx ▸ hxS⟩
  have hka : k ≤ a := Finset.le_max' old k hkOld
  have hxq : x ∈ q.support := by
    have hkq : k ≤ q.length := by omega
    have heq : q.getVert k = x := (SimpleGraph.Walk.getVert_takeUntil hw hkq).trans hkx
    exact heq ▸ q.getVert_mem_support k
  have hxtail : x ∈ r.support.tail := by
    have hh := hx
    rw [r.support_eq_cons] at hh
    rcases List.mem_cons.mp hh with hh | hh
    · exact False.elim (hxw hh)
    · exact hh
  exact List.disjoint_left.mp hdisjoint hxq hxtail

/-- The path graft does not add any vertices except those of its fresh tail. -/
theorem tree_path_graft_support_union (hT : T.IsAcyclic) (S : Set V) (hS : (T.induce S).Connected)
    (root v : V) (hr : root ∈ S) (p : T.Walk root v) (hp : p.IsPath) :
    ∃ (w : V) (hw : w ∈ p.support), w ∈ S ∧
      (p.dropUntil w hw).IsPath ∧
      (∀ x ∈ (p.dropUntil w hw).support, x ≠ w → x ∉ S) ∧
      (S ∪ {x | x ∈ p.support}) = S ∪ {x | x ∈ (p.dropUntil w hw).support} := by
  obtain ⟨w, hw, hwS, hprefix, hfresh, hpath, _⟩ := tree_path_graft_tail hT S hS root v hr p hp
  refine ⟨w, hw, hwS, hpath, hfresh, ?_⟩
  ext x
  constructor
  · rintro (hx | hx)
    · exact Or.inl hx
    · have hh : x ∈ (p.takeUntil w hw).support ∨ x ∈ (p.dropUntil w hw).support := by
        change x ∈ p.support at hx
        rw [← p.take_spec hw, SimpleGraph.Walk.mem_support_append_iff] at hx
        exact hx
      exact hh.elim (fun h => Or.inl (hprefix x h)) Or.inr
  · rintro (hx | hx)
    · exact Or.inl hx
    · exact Or.inr (p.support_dropUntil_subset hw hx)

end
end LocalLaw
