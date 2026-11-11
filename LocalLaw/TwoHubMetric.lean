import LocalLaw.TwoHubContact

/-! Actual metric bounds for two hubs attached to disconnected old components. -/
noncomputable section
namespace LocalLaw
local instance twoHubMetricDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V W : Type}

/-- A lifted old component remains connected in the augmented restriction. -/
theorem liftedComponent_reachable_twoHub (G : SimpleGraph V) (K L M : Set V)
    (c : (G.induce K).ConnectedComponent) (u v : twoHubVertices K L M)
    (hu : u.val ∈ liftedComponent G K c) (hv : v.val ∈ liftedComponent G K c) :
    (G.induce (twoHubVertices K L M)).Reachable u v := by
  obtain ⟨huK, huc⟩ := hu
  obtain ⟨hvK, hvc⟩ := hv
  have hr : (G.induce K).Reachable ⟨u.val, huK⟩ ⟨v.val, hvK⟩ :=
    SimpleGraph.ConnectedComponent.exact (huc.trans hvc.symm)
  let f : (G.induce K) →g G.induce (twoHubVertices K L M) :=
    { toFun := fun x => ⟨x.val, Or.inl x.property⟩
      map_rel' := fun h => h }
  exact hr.map f

/-- Contact costs at most one edge in any target graph reached by an
actual homomorphism from the augmented graph. -/
theorem twoHub_contact_edist (G : SimpleGraph V) (K L M : Set V)
    (H : SimpleGraph W) (f : (G.induce (twoHubVertices K L M)) →g H)
    (u v : twoHubVertices K L M) (h : u.val = v.val ∨ G.Adj u.val v.val) :
    H.edist (f u) (f v) ≤ 1 := by
  rcases h with heq | hadj
  · have hh : u = v := Subtype.ext heq
    subst v; simp
  · exact (SimpleGraph.edist_le (f.map_adj hadj).toWalk)

/-- A bridge through one old component controls the distance between the
actual two hub centers. -/
theorem twoHub_centers_edist (G : SimpleGraph V) (K L M : Set V)
    (H : SimpleGraph W) (f : (G.induce (twoHubVertices K L M)) →g H)
    (l m : twoHubVertices K L M) (hl : l.val ∈ L) (hm : m.val ∈ M)
    (D r : ℕ)
    (hK : ∀ c : (G.induce K).ConnectedComponent, ∀ u v : twoHubVertices K L M,
      u.val ∈ liftedComponent G K c → v.val ∈ liftedComponent G K c →
      H.edist (f u) (f v) ≤ (D : ℕ∞))
    (hL : ∀ u : twoHubVertices K L M, u.val ∈ L → H.edist (f l) (f u) ≤ (r : ℕ∞))
    (hM : ∀ u : twoHubVertices K L M, u.val ∈ M → H.edist (f m) (f u) ≤ (r : ℕ∞))
    (hr : (G.induce (twoHubVertices K L M)).Reachable l m) :
    H.edist (f l) (f m) ≤ ((2 * r + D + 2 : ℕ) : ℕ∞) := by
  rcases twoHub_bridge_of_reachable G K L M l m hl hm hr with hd | ⟨c, hcL, hcM⟩
  · obtain ⟨u, hu, v, hv, huv⟩ := hd
    let a : twoHubVertices K L M := ⟨u, Or.inr (Or.inl hu)⟩
    let b : twoHubVertices K L M := ⟨v, Or.inr (Or.inr hv)⟩
    have he := twoHub_contact_edist G K L M H f a b huv
    have hleft := hL a hu
    have hright : H.edist (f b) (f m) ≤ (r : ℕ∞) := by simpa only [SimpleGraph.edist_comm] using hM b hv
    have hh := (SimpleGraph.edist_triangle (G := H) (u := f l) (v := f a) (w := f m)).trans
      (add_le_add hleft ((SimpleGraph.edist_triangle (G := H) (u := f a) (v := f b) (w := f m)).trans
        (add_le_add he hright)))
    exact hh.trans (by exact_mod_cast (show r + (1 + r) ≤ 2*r+D+2 by omega))
  · obtain ⟨u, hu, a, ha, hua⟩ := hcL
    obtain ⟨v, hv, b, hb, hvb⟩ := hcM
    let uu : twoHubVertices K L M := ⟨u, Or.inl (Classical.choose hu)⟩
    let vv : twoHubVertices K L M := ⟨v, Or.inl (Classical.choose hv)⟩
    let aa : twoHubVertices K L M := ⟨a, Or.inr (Or.inl ha)⟩
    let bb : twoHubVertices K L M := ⟨b, Or.inr (Or.inr hb)⟩
    have hea : H.edist (f aa) (f uu) ≤ 1 := by
      simpa only [SimpleGraph.edist_comm] using twoHub_contact_edist G K L M H f uu aa hua
    have heb := twoHub_contact_edist G K L M H f vv bb hvb
    calc
      H.edist (f l) (f m) ≤ H.edist (f l) (f aa) + H.edist (f aa) (f m) := SimpleGraph.edist_triangle
      _ ≤ (r : ℕ∞) + (H.edist (f aa) (f uu) + H.edist (f uu) (f m)) :=
        add_le_add (hL aa ha) SimpleGraph.edist_triangle
      _ ≤ (r : ℕ∞) + (1 + (H.edist (f uu) (f vv) + H.edist (f vv) (f m))) :=
        add_le_add_left (add_le_add hea SimpleGraph.edist_triangle) _
      _ ≤ (r : ℕ∞) + (1 + ((D : ℕ∞) + (H.edist (f vv) (f bb) + H.edist (f bb) (f m)))) :=
        add_le_add_left (add_le_add_left (add_le_add (hK c uu vv hu hv) SimpleGraph.edist_triangle) _) _
      _ ≤ (r : ℕ∞) + (1 + ((D : ℕ∞) + (1 + (r : ℕ∞)))) := by
        apply add_le_add_left
        apply add_le_add_left
        apply add_le_add_left
        exact add_le_add heb (by simpa only [SimpleGraph.edist_comm] using hM bb hb)
      _ = ((2*r+D+2 : ℕ) : ℕ∞) := by push_cast; ring

/-- A vertex in the hub component is close to one of its two centers;
the chosen center is genuinely connected to it in the induced union. -/
theorem twoHub_entry_center (G : SimpleGraph V) (K L M : Set V)
    (H : SimpleGraph W) (f : (G.induce (twoHubVertices K L M)) →g H)
    (l m : twoHubVertices K L M) (D r : ℕ)
    (hK : ∀ c : (G.induce K).ConnectedComponent, ∀ u v : twoHubVertices K L M,
      u.val ∈ liftedComponent G K c → v.val ∈ liftedComponent G K c →
      H.edist (f u) (f v) ≤ (D : ℕ∞))
    (hL : ∀ u : twoHubVertices K L M, u.val ∈ L →
      H.edist (f l) (f u) ≤ (r : ℕ∞) ∧ (G.induce (twoHubVertices K L M)).Reachable u l)
    (hM : ∀ u : twoHubVertices K L M, u.val ∈ M →
      H.edist (f m) (f u) ≤ (r : ℕ∞) ∧ (G.induce (twoHubVertices K L M)).Reachable u m)
    (a b : twoHubVertices K L M) (hb : b.val ∈ L ∪ M)
    (hr : (G.induce (twoHubVertices K L M)).Reachable a b) :
    ∃ center, (center = l ∨ center = m) ∧
      H.edist (f a) (f center) ≤ ((D + r + 1 : ℕ) : ℕ∞) ∧
      (G.induce (twoHubVertices K L M)).Reachable a center := by
  have hub (u : twoHubVertices K L M) (hu : u.val ∈ L ∪ M) :
      ∃ center, (center = l ∨ center = m) ∧ H.edist (f u) (f center) ≤ (r : ℕ∞) ∧
        (G.induce (twoHubVertices K L M)).Reachable u center := by
    rcases hu with hu | hu
    · exact ⟨l, Or.inl rfl, by simpa only [SimpleGraph.edist_comm] using (hL u hu).1, (hL u hu).2⟩
    · exact ⟨m, Or.inr rfl, by simpa only [SimpleGraph.edist_comm] using (hM u hu).1, (hM u hu).2⟩
  rcases twoHub_entry_of_reachable G K L M a b hb hr with ha | ⟨c, hac, hc⟩
  · obtain ⟨center, hc, hd, hr⟩ := hub a ha
    exact ⟨center, hc, hd.trans (ENat.coe_le_coe.mpr (by omega)), hr⟩
  · obtain ⟨u, hu, v, hv, huv⟩ := hc
    let uu : twoHubVertices K L M := ⟨u, Or.inl (Classical.choose hu)⟩
    let vv : twoHubVertices K L M := ⟨v, Or.inr hv⟩
    obtain ⟨center, hcenter, hd, hreach⟩ := hub vv hv
    have he := twoHub_contact_edist G K L M H f uu vv huv
    have hdist := (SimpleGraph.edist_triangle (G := H) (u := f a) (v := f uu) (w := f center)).trans
      (add_le_add (hK c a uu hac hu) ((SimpleGraph.edist_triangle (G := H) (u := f uu) (v := f vv) (w := f center)).trans
      (add_le_add he hd)))
    have hstep : (G.induce (twoHubVertices K L M)).Reachable uu vv := by
      rcases huv with h | h
      · exact (show uu = vv from Subtype.ext h) ▸ SimpleGraph.Reachable.refl _
      · exact (show (G.induce (twoHubVertices K L M)).Adj uu vv from h).reachable
    refine ⟨center, hcenter, ?_, (liftedComponent_reachable_twoHub G K L M c a uu hac hu).trans (hstep.trans hreach)⟩
    apply hdist.trans_eq
    push_cast
    ring

/-- Every vertex connected to the first hub is within `3r+2D+3` of
its center, in the actual target metric. -/
theorem twoHub_center_enclosure (G : SimpleGraph V) (K L M : Set V)
    (H : SimpleGraph W) (f : (G.induce (twoHubVertices K L M)) →g H)
    (l m : twoHubVertices K L M) (hl : l.val ∈ L) (hm : m.val ∈ M) (D r : ℕ)
    (hK : ∀ c : (G.induce K).ConnectedComponent, ∀ u v : twoHubVertices K L M,
      u.val ∈ liftedComponent G K c → v.val ∈ liftedComponent G K c →
      H.edist (f u) (f v) ≤ (D : ℕ∞))
    (hL : ∀ u : twoHubVertices K L M, u.val ∈ L →
      H.edist (f l) (f u) ≤ (r : ℕ∞) ∧ (G.induce (twoHubVertices K L M)).Reachable u l)
    (hM : ∀ u : twoHubVertices K L M, u.val ∈ M →
      H.edist (f m) (f u) ≤ (r : ℕ∞) ∧ (G.induce (twoHubVertices K L M)).Reachable u m)
    (a : twoHubVertices K L M) (hr : (G.induce (twoHubVertices K L M)).Reachable l a) :
    H.edist (f l) (f a) ≤ ((3*r+2*D+3 : ℕ) : ℕ∞) := by
  obtain ⟨center, hc, hd, hreach⟩ := twoHub_entry_center G K L M H f l m D r hK hL hM a l (Or.inl hl) hr.symm
  have hcent : H.edist (f l) (f center) ≤ ((2*r+D+2 : ℕ) : ℕ∞) := by
    rcases hc with hc | hc
    · rw [hc]; simp
    · rw [hc]
      exact twoHub_centers_edist G K L M H f l m hl hm D r hK
        (fun u hu => (hL u hu).1) (fun u hu => (hM u hu).1)
        (hr.trans (by simpa only [hc] using hreach))
  have hd' : H.edist (f center) (f a) ≤ ((D+r+1 : ℕ) : ℕ∞) := by
    simpa only [SimpleGraph.edist_comm] using hd
  exact ((SimpleGraph.edist_triangle (G := H) (u := f l) (v := f center) (w := f a)).trans
    (add_le_add hcent hd')).trans_eq (by push_cast; ring)

/-- If the component never meets either hub, an actual connecting walk
stays in one old induced component. -/
theorem twoHub_no_hub_same_component (G : SimpleGraph V) (K L M : Set V)
    (a b : twoHubVertices K L M)
    (hr : (G.induce (twoHubVertices K L M)).Reachable a b)
    (hn : ¬∃ v : twoHubVertices K L M, v.val ∈ L ∪ M ∧
      (G.induce (twoHubVertices K L M)).Reachable a v) :
    ∃ c : (G.induce K).ConnectedComponent,
      a.val ∈ liftedComponent G K c ∧ b.val ∈ liftedComponent G K c := by
  have haH : a.val ∉ L ∪ M := fun h => hn ⟨a,h,SimpleGraph.Reachable.refl _⟩
  have haK : a.val ∈ K := a.property.resolve_right haH
  let c := (G.induce K).connectedComponentMk ⟨a.val,haK⟩
  have hac : a.val ∈ liftedComponent G K c := ⟨haK,rfl⟩
  refine ⟨c,hac,?_⟩
  by_contra hbc
  obtain ⟨p⟩ := hr
  obtain ⟨u,hu,v,hv,huv⟩ := walk_crosses_cut (G.induce (twoHubVertices K L M)) p
    {v | v.val ∈ liftedComponent G K c} hac hbc
  have hvH : v.val ∈ L ∪ M := by
    rcases v.property with hvK | hvH
    · exact False.elim (hv (liftedComponent_adj_closed G K c hu hvK huv))
    · exact hvH
  exact hn ⟨v,hvH,(liftedComponent_reachable_twoHub G K L M c a u hac hu).trans huv.reachable⟩

/-- Two hubs can join arbitrarily many old components, but a shortest
connection uses at most three old component segments. -/
theorem twoHub_reachable_edist_bound (G : SimpleGraph V) (K L M : Set V)
    (H : SimpleGraph W) (f : (G.induce (twoHubVertices K L M)) →g H)
    (l m : twoHubVertices K L M) (hl : l.val ∈ L) (hm : m.val ∈ M) (D r : ℕ)
    (hK : ∀ c : (G.induce K).ConnectedComponent, ∀ u v : twoHubVertices K L M,
      u.val ∈ liftedComponent G K c → v.val ∈ liftedComponent G K c →
      H.edist (f u) (f v) ≤ (D : ℕ∞))
    (hL : ∀ u : twoHubVertices K L M, u.val ∈ L →
      H.edist (f l) (f u) ≤ (r : ℕ∞) ∧ (G.induce (twoHubVertices K L M)).Reachable u l)
    (hM : ∀ u : twoHubVertices K L M, u.val ∈ M →
      H.edist (f m) (f u) ≤ (r : ℕ∞) ∧ (G.induce (twoHubVertices K L M)).Reachable u m)
    (a b : twoHubVertices K L M) (hr : (G.induce (twoHubVertices K L M)).Reachable a b) :
    H.edist (f a) (f b) ≤ ((3*D+4*r+4 : ℕ) : ℕ∞) := by
  by_cases hex : ∃ v : twoHubVertices K L M, v.val ∈ L ∪ M ∧
      (G.induce (twoHubVertices K L M)).Reachable a v
  · obtain ⟨v,hv,hav⟩ := hex
    obtain ⟨ca,hca,hda,hra⟩ := twoHub_entry_center G K L M H f l m D r hK hL hM a v hv hav
    obtain ⟨cb,hcb,hdb,hrb⟩ := twoHub_entry_center G K L M H f l m D r hK hL hM b v hv (hr.symm.trans hav)
    have hrcc := hra.symm.trans (hr.trans hrb)
    have hcc : H.edist (f ca) (f cb) ≤ ((2*r+D+2 : ℕ) : ℕ∞) := by
      rcases hca with hca | hca <;> rcases hcb with hcb | hcb
      · rw [hca,hcb]; simp
      · rw [hca,hcb]
        exact twoHub_centers_edist G K L M H f l m hl hm D r hK
          (fun u hu => (hL u hu).1) (fun u hu => (hM u hu).1)
          (by simpa only [hca,hcb] using hrcc)
      · rw [hca,hcb]
        simpa only [SimpleGraph.edist_comm] using twoHub_centers_edist G K L M H f l m hl hm D r hK
          (fun u hu => (hL u hu).1) (fun u hu => (hM u hu).1)
          (by simpa only [hca,hcb] using hrcc.symm)
      · rw [hca,hcb]; simp
    calc
      H.edist (f a) (f b) ≤ H.edist (f a) (f ca) + H.edist (f ca) (f b) := SimpleGraph.edist_triangle
      _ ≤ ((D+r+1 : ℕ) : ℕ∞) + (H.edist (f ca) (f cb) + H.edist (f cb) (f b)) :=
        add_le_add hda SimpleGraph.edist_triangle
      _ ≤ ((D+r+1 : ℕ) : ℕ∞) + (((2*r+D+2 : ℕ) : ℕ∞) + ((D+r+1 : ℕ) : ℕ∞)) := by
        exact add_le_add_left (add_le_add hcc (by simpa only [SimpleGraph.edist_comm] using hdb)) _
      _ = _ := by push_cast; ring
  · obtain ⟨c,hac,hbc⟩ := twoHub_no_hub_same_component G K L M a b hr hex
    exact (hK c a b hac hbc).trans (ENat.coe_le_coe.mpr (by omega))

end LocalLaw
