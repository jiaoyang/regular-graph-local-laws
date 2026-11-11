import LocalLaw.PendantTreePatch

/-!
# Short walks that avoid a tree patch's own attachment stay inside the patch

No old outward edge can be reached within R, and the other attachment root
is separated by deleting the bridge b-c. Therefore every length-at-most-R
walk from b avoiding its attachment b-a lifts into the actual deleted old
tree. This path-locality lemma is used to identify the finitely many coreward
switchings visible from the center of a large switched ball.
-/

noncomputable section
namespace LocalLaw

local instance shortPatchWalksDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*}

theorem short_walk_avoiding_patch_entry_with_support (G H : SimpleGraph V) (W : Set V)
    (b c a l : V) (hb : b ∈ W) (hc : c ∈ W) (hbc : G.Adj b c)
    (htree : (G.induce W).IsTree) (R : ℕ)
    (hfar : ∀ v ∉ W, (R : ℕ∞) < G.edist b v)
    (hinside : ∀ u v : W, H.Adj u.val v.val →
      ((G.induce W) \ SimpleGraph.edge (⟨b, hb⟩ : W) (⟨c, hc⟩ : W)).Adj u v)
    (hcross : ∀ u ∈ W, ∀ v ∉ W, H.Adj u v → G.Adj u v ∨
      (u = b ∧ v = a) ∨ (u = c ∧ v = l))
    {v : V} (p : H.Walk b v) (hlen : p.length ≤ R) (hentry : s(b, a) ∉ p.edges) :
    ∃ hv : v ∈ W, ∃ q : ((G.induce W) \ SimpleGraph.edge (⟨b, hb⟩ : W) (⟨c, hc⟩ : W)).Walk
      ⟨b, hb⟩ ⟨v, hv⟩, q.length = p.length ∧ ∀ w ∈ p.support, w ∈ W := by
  classical
  let D := (G.induce W) \ SimpleGraph.edge (⟨b, hb⟩ : W) (⟨c, hc⟩ : W)
  have hbridge : (G.induce W).IsBridge s((⟨b, hb⟩ : W), (⟨c, hc⟩ : W)) :=
    (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp htree.IsAcyclic) hbc
  have hNoReach : ¬ D.Reachable (⟨b, hb⟩ : W) (⟨c, hc⟩ : W) :=
    (SimpleGraph.isBridge_iff.mp hbridge).2
  let fOld : D →g G := { toFun := Subtype.val, map_rel' := fun h => h.1 }
  have haux : ∀ {u v : V} (p : H.Walk u v), u = b → p.length ≤ R → s(b, a) ∉ p.edges →
      ∃ hv : v ∈ W, ∃ q : D.Walk ⟨b, hb⟩ ⟨v, hv⟩,
        q.length = p.length ∧ ∀ w ∈ p.support, w ∈ W := by
    intro u v p
    induction p using SimpleGraph.Walk.concatRec with
    | Hnil =>
      intro hu _ _
      cases hu
      exact ⟨hb, SimpleGraph.Walk.nil, rfl, by simpa using hb⟩
    | @Hconcat u w v p hwv ih =>
      intro hub hlen hentry
      have hlenP : p.length ≤ R := by simp only [SimpleGraph.Walk.length_concat] at hlen; omega
      have hentryP : s(b, a) ∉ p.edges := by
        intro he
        exact hentry (by simp only [SimpleGraph.Walk.edges_concat, List.concat_eq_append, List.mem_append, List.mem_singleton]; exact Or.inl he)
      have hlast : s(b, a) ≠ s(w, v) := by
        intro he
        apply hentry
        simp only [SimpleGraph.Walk.edges_concat, List.concat_eq_append, List.mem_append, List.mem_singleton]
        exact Or.inr he
      obtain ⟨hw, q, hq, hsupp⟩ := ih hub hlenP hentryP
      have hv : v ∈ W := by
        by_cases hv : v ∈ W
        · exact hv
        apply False.elim
        rcases hcross w hw v hv hwv with hold | ⟨hwb, hva⟩ | ⟨hwc, hvl⟩
        · let oldp := (q.map fOld).concat hold
          have hd : G.edist b v ≤ (R : ℕ∞) := (G.edist_le oldp).trans (by
            simpa only [oldp, SimpleGraph.Walk.length_concat, SimpleGraph.Walk.length_map, hq] using
              ENat.coe_le_coe.mpr hlen)
          exact (not_lt_of_ge hd) (hfar v hv)
        · exact hlast (by rw [hwb, hva])
        · have heq : (⟨w, hw⟩ : W) = (⟨c, hc⟩ : W) := Subtype.ext hwc
          apply hNoReach
          rw [← heq]
          exact q.reachable
      refine ⟨hv, q.concat (hinside ⟨w, hw⟩ ⟨v, hv⟩ hwv), ?_, ?_⟩
      · simp only [SimpleGraph.Walk.length_concat, hq]
      · intro z hz
        simp only [SimpleGraph.Walk.support_concat, List.concat_eq_append,
          List.mem_append, List.mem_singleton] at hz
        exact hz.elim (hsupp z) (fun h => h ▸ hv)
  exact haux p rfl hlen hentry

theorem short_walk_avoiding_patch_entry (G H : SimpleGraph V) (W : Set V)
    (b c a l : V) (hb : b ∈ W) (hc : c ∈ W) (hbc : G.Adj b c)
    (htree : (G.induce W).IsTree) (R : ℕ)
    (hfar : ∀ v ∉ W, (R : ℕ∞) < G.edist b v)
    (hinside : ∀ u v : W, H.Adj u.val v.val →
      ((G.induce W) \ SimpleGraph.edge (⟨b, hb⟩ : W) (⟨c, hc⟩ : W)).Adj u v)
    (hcross : ∀ u ∈ W, ∀ v ∉ W, H.Adj u v → G.Adj u v ∨
      (u = b ∧ v = a) ∨ (u = c ∧ v = l))
    {v : V} (p : H.Walk b v) (hlen : p.length ≤ R) (hentry : s(b, a) ∉ p.edges) :
    ∃ hv : v ∈ W, ∃ q : ((G.induce W) \ SimpleGraph.edge (⟨b, hb⟩ : W) (⟨c, hc⟩ : W)).Walk
      ⟨b, hb⟩ ⟨v, hv⟩, q.length = p.length := by
  obtain ⟨hv, q, hq, _⟩ := short_walk_avoiding_patch_entry_with_support G H W b c a l hb hc
    hbc htree R hfar hinside hcross p hlen hentry
  exact ⟨hv, q, hq⟩

/-- A simple path approaching an attachment from its tree side must have
started in the tree patch. This also controls every preceding vertex. -/
theorem short_path_before_patch_entry_support (G H : SimpleGraph V) (W : Set V)
    (b c a l : V) (hb : b ∈ W) (hc : c ∈ W) (hbc : G.Adj b c)
    (htree : (G.induce W).IsTree) (R : ℕ)
    (hfar : ∀ v ∉ W, (R : ℕ∞) < G.edist b v)
    (hinside : ∀ u v : W, H.Adj u.val v.val →
      ((G.induce W) \ SimpleGraph.edge (⟨b, hb⟩ : W) (⟨c, hc⟩ : W)).Adj u v)
    (hcross : ∀ u ∈ W, ∀ v ∉ W, H.Adj u v → G.Adj u v ∨
      (u = b ∧ v = a) ∨ (u = c ∧ v = l))
    {x : V} (p : H.Walk x b) (hba : H.Adj b a) (hp : (p.concat hba).IsPath)
    (hlen : p.length ≤ R) : ∀ w ∈ p.support, w ∈ W := by
  have hnot : a ∉ p.support := by
    have hr := hp.reverse
    rw [SimpleGraph.Walk.reverse_concat] at hr
    have ha := (SimpleGraph.Walk.cons_isPath_iff _ _).mp hr |>.2
    simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using ha
  have hentry : s(b, a) ∉ p.reverse.edges := by
    intro he
    rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse] at he
    exact hnot (p.snd_mem_support_of_mem_edges he)
  obtain ⟨_, _, _, hsupp⟩ := short_walk_avoiding_patch_entry_with_support G H W b c a l hb hc
    hbc htree R hfar hinside hcross p.reverse (by simpa using hlen) hentry
  intro w hw
  exact hsupp w (by simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hw)

end LocalLaw
