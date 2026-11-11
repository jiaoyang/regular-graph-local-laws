import Mathlib

/-!
# Construct post-switch component labels from actual branch partitions

A central old graph is joined to the b-side of each split sampled tree; the
c-side remains detached. A label is constructed on every vertex and proved
constant along every permitted post edge and walk. No post-component label
or endpoint-fiber conclusion is assumed.
-/

noncomputable section
namespace LocalLaw
local instance postClassifierDecidable (p : Prop) : Decidable p := Classical.propDecidable p

structure BranchAttachmentData (V I : Type*) (old post : SimpleGraph V) where
  core : Set V
  B : I → Set V
  C : I → Set V
  attach : I → V
  base : I → V
  tip : I → V
  attach_mem : ∀ i, attach i ∈ core
  base_mem : ∀ i, base i ∈ B i
  tip_mem : ∀ i, tip i ∈ C i
  core_disjoint : ∀ i, Disjoint core (B i ∪ C i)
  branch_disjoint : ∀ i, Disjoint (B i) (C i)
  family_disjoint : ∀ i j, i ≠ j → Disjoint (B i ∪ C i) (B j ∪ C j)
  cover : ∀ v, v ∉ core → ∃ i, v ∈ B i ∨ v ∈ C i
  attach_edge : ∀ i, post.Adj (attach i) (base i)
  edge_cover : ∀ {u v}, post.Adj u v →
    (u ∈ core ∧ v ∈ core ∧ old.Adj u v) ∨
      (∃ i, u ∈ B i ∧ v ∈ B i) ∨
      (∃ i, u ∈ C i ∧ v ∈ C i) ∨
      (∃ i, (u = attach i ∧ v = base i) ∨ (v = attach i ∧ u = base i))

namespace BranchAttachmentData
variable {V I : Type*} {old post : SimpleGraph V}

def branchIndex (D : BranchAttachmentData V I old post) (v : V) (hv : v ∉ D.core) : I :=
  Classical.choose (D.cover v hv)

theorem branchIndex_mem (D : BranchAttachmentData V I old post) (v : V) (hv : v ∉ D.core) :
    v ∈ D.B (D.branchIndex v hv) ∨ v ∈ D.C (D.branchIndex v hv) :=
  Classical.choose_spec (D.cover v hv)

theorem not_core_of_branch (D : BranchAttachmentData V I old post) (i : I) (v : V)
    (hv : v ∈ D.B i ∨ v ∈ D.C i) : v ∉ D.core :=
  fun hc => Set.disjoint_left.mp (D.core_disjoint i) hc hv

theorem branchIndex_eq (D : BranchAttachmentData V I old post) (v : V) (hv : v ∉ D.core)
    (i : I) (hi : v ∈ D.B i ∨ v ∈ D.C i) : D.branchIndex v hv = i := by
  by_contra h
  exact Set.disjoint_left.mp (D.family_disjoint _ i h) (D.branchIndex_mem v hv) hi

def vertexLabel (D : BranchAttachmentData V I old post) (v : V) :
    (old.induce D.core).ConnectedComponent ⊕ I :=
  if hv : v ∈ D.core then Sum.inl ((old.induce D.core).connectedComponentMk ⟨v, hv⟩)
  else if v ∈ D.B (D.branchIndex v hv) then
    Sum.inl ((old.induce D.core).connectedComponentMk ⟨D.attach (D.branchIndex v hv), D.attach_mem _⟩)
  else Sum.inr (D.branchIndex v hv)

theorem vertexLabel_core (D : BranchAttachmentData V I old post) (v : V) (hv : v ∈ D.core) :
    D.vertexLabel v = Sum.inl ((old.induce D.core).connectedComponentMk ⟨v, hv⟩) := by
  simp only [vertexLabel, dif_pos hv]

theorem vertexLabel_B (D : BranchAttachmentData V I old post) (i : I) (v : V) (hv : v ∈ D.B i) :
    D.vertexLabel v = Sum.inl ((old.induce D.core).connectedComponentMk ⟨D.attach i, D.attach_mem i⟩) := by
  have hc := D.not_core_of_branch i v (Or.inl hv)
  have hi := D.branchIndex_eq v hc i (Or.inl hv)
  simp only [vertexLabel, dif_neg hc, hi, if_pos hv]

theorem vertexLabel_C (D : BranchAttachmentData V I old post) (i : I) (v : V) (hv : v ∈ D.C i) :
    D.vertexLabel v = Sum.inr i := by
  have hc := D.not_core_of_branch i v (Or.inr hv)
  have hi := D.branchIndex_eq v hc i (Or.inr hv)
  have hB : v ∉ D.B i := fun h => Set.disjoint_left.mp (D.branch_disjoint i) h hv
  simp only [vertexLabel, dif_neg hc, hi, if_neg hB]

/-- The labels are derived from the literal post-edge cover. -/
theorem vertexLabel_eq_of_adj (D : BranchAttachmentData V I old post) {u v : V} (h : post.Adj u v) :
    D.vertexLabel u = D.vertexLabel v := by
  rcases D.edge_cover h with ⟨hu, hv, huv⟩ | ⟨i, hu, hv⟩ | ⟨i, hu, hv⟩ | ⟨i, h | h⟩
  · rw [D.vertexLabel_core u hu, D.vertexLabel_core v hv]
    exact congrArg Sum.inl (SimpleGraph.ConnectedComponent.sound
      (show (old.induce D.core).Adj ⟨u, hu⟩ ⟨v, hv⟩ from huv).reachable)
  · rw [D.vertexLabel_B i u hu, D.vertexLabel_B i v hv]
  · rw [D.vertexLabel_C i u hu, D.vertexLabel_C i v hv]
  · rcases h with ⟨rfl, rfl⟩
    rw [D.vertexLabel_core _ (D.attach_mem i), D.vertexLabel_B _ _ (D.base_mem i)]
  · rcases h with ⟨rfl, rfl⟩
    rw [D.vertexLabel_B _ _ (D.base_mem i), D.vertexLabel_core _ (D.attach_mem i)]

theorem vertexLabel_eq_of_walk (D : BranchAttachmentData V I old post) {u v : V} (p : post.Walk u v) :
    D.vertexLabel u = D.vertexLabel v := by
  induction p with
  | nil => rfl
  | cons h p ih => exact (D.vertexLabel_eq_of_adj h).trans ih

theorem vertexLabel_eq_of_reachable (D : BranchAttachmentData V I old post) {u v : V}
    (h : post.Reachable u v) : D.vertexLabel u = D.vertexLabel v := by
  obtain ⟨p⟩ := h
  exact D.vertexLabel_eq_of_walk p

def centralLabel (D : BranchAttachmentData V I old post) (i : I) : (old.induce D.core).ConnectedComponent :=
  (old.induce D.core).connectedComponentMk ⟨D.attach i, D.attach_mem i⟩

def endpoint (D : BranchAttachmentData V I old post) (p : I × Fin 3) : V :=
  Fin.cases (D.attach p.1) (fun k => Fin.cases (D.base p.1) (fun _ => D.tip p.1) k) p.2

theorem vertexLabel_endpoint (D : BranchAttachmentData V I old post) (p : I × Fin 3) :
    D.vertexLabel (D.endpoint p) = if p.2 = 2 then Sum.inr p.1 else Sum.inl (D.centralLabel p.1) := by
  rcases p with ⟨i, t⟩
  fin_cases t
  · exact D.vertexLabel_core _ (D.attach_mem i)
  · exact D.vertexLabel_B _ _ (D.base_mem i)
  · exact D.vertexLabel_C _ _ (D.tip_mem i)

/-- Post-connected central endpoints retain their actual old central component. -/
theorem centralLabel_eq_of_attach_reachable (D : BranchAttachmentData V I old post) {i j : I}
    (h : post.Reachable (D.attach i) (D.attach j)) : D.centralLabel i = D.centralLabel j := by
  have hh := D.vertexLabel_eq_of_reachable h
  rw [D.vertexLabel_core _ (D.attach_mem i), D.vertexLabel_core _ (D.attach_mem j)] at hh
  exact Sum.inl.inj hh

/-- Distinct detached branches cannot be post-connected. -/
theorem tip_index_eq_of_reachable (D : BranchAttachmentData V I old post) {i j : I}
    (h : post.Reachable (D.tip i) (D.tip j)) : i = j := by
  have hh := D.vertexLabel_eq_of_reachable h
  rw [D.vertexLabel_C _ _ (D.tip_mem i), D.vertexLabel_C _ _ (D.tip_mem j)] at hh
  exact Sum.inr.inj hh

/-- No detached branch endpoint belongs to a post central component. -/
theorem not_attach_reachable_tip (D : BranchAttachmentData V I old post) (i j : I) :
    ¬post.Reachable (D.attach i) (D.tip j) := by
  intro h
  have hh := D.vertexLabel_eq_of_reachable h
  rw [D.vertexLabel_core _ (D.attach_mem i), D.vertexLabel_C _ _ (D.tip_mem j)] at hh
  exact Sum.noConfusion hh

/-- The endpoint index includes every old central root, including roots whose
sample is rejected, and the two sampled endpoints for each accepted label. -/
def fullEndpoint {J : Type*} (D : BranchAttachmentData V I old post)
    (root : J → V) (p : J ⊕ (I × Fin 2)) : V :=
  match p with
  | Sum.inl j => root j
  | Sum.inr (i, t) => if t = 0 then D.base i else D.tip i

def rootLabel {J : Type*} (D : BranchAttachmentData V I old post)
    (root : J → V) (hroot : ∀ j, root j ∈ D.core) (j : J) :
    (old.induce D.core).ConnectedComponent :=
  (old.induce D.core).connectedComponentMk ⟨root j, hroot j⟩

theorem fullEndpoint_label_left {J : Type*} (D : BranchAttachmentData V I old post)
    (root : J → V) (hroot : ∀ j, root j ∈ D.core) (j : J) :
    D.vertexLabel (D.fullEndpoint root (Sum.inl j)) = Sum.inl (D.rootLabel root hroot j) :=
  D.vertexLabel_core _ (hroot j)

theorem fullEndpoint_label_right {J : Type*} (D : BranchAttachmentData V I old post)
    (root : J → V) (i : I) (t : Fin 2) :
    D.vertexLabel (D.fullEndpoint root (Sum.inr (i, t))) =
      if t = 0 then Sum.inl (D.centralLabel i) else Sum.inr i := by
  fin_cases t
  · exact D.vertexLabel_B _ _ (D.base_mem i)
  · exact D.vertexLabel_C _ _ (D.tip_mem i)

/-- Exact central endpoint incidence, with both accepted and unaccepted old roots. -/
def centralEndpointFiberEquiv {J : Type*} (D : BranchAttachmentData V I old post)
    (root : J → V) (hroot : ∀ j, root j ∈ D.core)
    (c : (old.induce D.core).ConnectedComponent) :
    {p : J ⊕ (I × Fin 2) // D.vertexLabel (D.fullEndpoint root p) = Sum.inl c} ≃
      ({j : J // D.rootLabel root hroot j = c} ⊕ {i : I // D.centralLabel i = c}) where
  toFun p := by
    rcases p with ⟨j | ⟨i,t⟩, h⟩
    · exact Sum.inl ⟨j, Sum.inl.inj ((D.fullEndpoint_label_left root hroot j).symm.trans h)⟩
    · have ht : t = 0 := by
        by_contra hn
        have hh := (D.fullEndpoint_label_right root i t).symm.trans h
        rw [if_neg hn] at hh
        exact Sum.noConfusion hh
      exact Sum.inr ⟨i, by
        subst t
        exact Sum.inl.inj ((D.fullEndpoint_label_right root i 0).symm.trans h)⟩
  invFun p := by
    rcases p with ⟨j,h⟩ | ⟨i,h⟩
    · exact ⟨Sum.inl j, (D.fullEndpoint_label_left root hroot j).trans (congrArg Sum.inl h)⟩
    · exact ⟨Sum.inr (i,0), (D.fullEndpoint_label_right root i 0).trans (by simp only [if_pos rfl]; exact congrArg Sum.inl h)⟩
  left_inv p := by
    rcases p with ⟨j | ⟨i,t⟩, h⟩
    · rfl
    · fin_cases t
      · rfl
      · have hh := (D.fullEndpoint_label_right root i 1).symm.trans h
        simp only [Fin.isValue, one_ne_zero, if_false] at hh
        exact Sum.noConfusion hh
  right_inv p := by cases p <;> rfl

theorem centralEndpointFiber_card {J : Type*} [Finite I] [Finite J]
    (D : BranchAttachmentData V I old post) (root : J → V)
    (hroot : ∀ j, root j ∈ D.core) (c : (old.induce D.core).ConnectedComponent) :
    Nat.card {p : J ⊕ (I × Fin 2) // D.vertexLabel (D.fullEndpoint root p) = Sum.inl c} =
      Nat.card {j : J // D.rootLabel root hroot j = c} +
        Nat.card {i : I // D.centralLabel i = c} := by
  rw [Nat.card_congr (D.centralEndpointFiberEquiv root hroot c), Nat.card_sum]

theorem detachedEndpointFiber_unique {J : Type*} (D : BranchAttachmentData V I old post)
    (root : J → V) (hroot : ∀ j, root j ∈ D.core) (i : I)
    (p : J ⊕ (I × Fin 2))
    (hp : D.vertexLabel (D.fullEndpoint root p) = Sum.inr i) : p = Sum.inr (i,1) := by
  rcases p with j | ⟨k,t⟩
  · have hh := (D.fullEndpoint_label_left root hroot j).symm.trans hp
    exact Sum.noConfusion hh
  · fin_cases t
    · have hh := (D.fullEndpoint_label_right root k 0).symm.trans hp
      simp only [Fin.isValue, ↓reduceIte] at hh
      exact Sum.noConfusion hh
    · have hh := (D.fullEndpoint_label_right root k 1).symm.trans hp
      simp only [Fin.isValue, one_ne_zero, if_false] at hh
      exact congrArg (fun k => Sum.inr (k, (1 : Fin 2))) (Sum.inr.inj hh)

theorem detachedEndpointFiber_card_le_one {J : Type*} (D : BranchAttachmentData V I old post)
    (root : J → V) (hroot : ∀ j, root j ∈ D.core) (i : I) :
    Nat.card {p : J ⊕ (I × Fin 2) // D.vertexLabel (D.fullEndpoint root p) = Sum.inr i} ≤ 1 := by
  classical
  let f : {p : J ⊕ (I × Fin 2) // D.vertexLabel (D.fullEndpoint root p) = Sum.inr i} → Unit := fun _ => ()
  have hf : Function.Injective f := by
    intro p q h
    apply Subtype.ext
    exact (D.detachedEndpointFiber_unique root hroot i p.val p.property).trans
      (D.detachedEndpointFiber_unique root hroot i q.val q.property).symm
  simpa using Nat.card_le_card_of_injective f hf

/-- Accepted roots inject into the complete old boundary-label family. -/
theorem attachFiber_card_le_rootFiber {J : Type*} [Finite I] [Finite J]
    (D : BranchAttachmentData V I old post) (root : J → V)
    (hroot : ∀ j, root j ∈ D.core) (select : I → J)
    (hinj : Function.Injective select) (hselect : ∀ i, D.attach i = root (select i))
    (c : (old.induce D.core).ConnectedComponent) :
    Nat.card {i : I // D.centralLabel i = c} ≤
      Nat.card {j : J // D.rootLabel root hroot j = c} := by
  have hl (i : I) : D.rootLabel root hroot (select i) = D.centralLabel i := by
    unfold rootLabel centralLabel
    congr 1
    exact Subtype.ext (hselect i).symm
  exact Nat.card_le_card_of_injective
    (fun i : {i : I // D.centralLabel i = c} => ⟨select i.val, (hl i.val).trans i.property⟩)
    (by intro i j h; exact Subtype.ext (hinj (congrArg Subtype.val h)))

/-- If the literal core edges persist and each actual branch remains connected,
constructed equal labels are exactly post reachability. -/
theorem reachable_iff_vertexLabel_eq (D : BranchAttachmentData V I old post)
    (hcore : ∀ {u v}, u ∈ D.core → v ∈ D.core → old.Adj u v → post.Adj u v)
    (hB : ∀ i, (post.induce (D.B i)).Preconnected)
    (hC : ∀ i, (post.induce (D.C i)).Preconnected) (u v : V) :
    post.Reachable u v ↔ D.vertexLabel u = D.vertexLabel v := by
  refine ⟨D.vertexLabel_eq_of_reachable, ?_⟩
  have coreReach {a b : V} (ha : a ∈ D.core) (hb : b ∈ D.core)
      (h : (old.induce D.core).connectedComponentMk ⟨a,ha⟩ =
        (old.induce D.core).connectedComponentMk ⟨b,hb⟩) : post.Reachable a b := by
    let f : (old.induce D.core) →g post :=
      ⟨Subtype.val, fun {x y} h => hcore x.property y.property h⟩
    exact (SimpleGraph.ConnectedComponent.exact h).map f
  have branchReach (i : I) {a b : V} (ha : a ∈ D.B i) (hb : b ∈ D.B i) :
      post.Reachable a b :=
    (hB i ⟨a,ha⟩ ⟨b,hb⟩).map ⟨Subtype.val, fun {_ _} h => h⟩
  have tipReach (i : I) {a b : V} (ha : a ∈ D.C i) (hb : b ∈ D.C i) :
      post.Reachable a b :=
    (hC i ⟨a,ha⟩ ⟨b,hb⟩).map ⟨Subtype.val, fun {_ _} h => h⟩
  have toCore (a : V) (ha : a ∉ D.core) (h : a ∈ D.B (D.branchIndex a ha)) :
      post.Reachable a (D.attach (D.branchIndex a ha)) :=
    (branchReach _ h (D.base_mem _)).trans (D.attach_edge _).symm.reachable
  intro huv
  by_cases hu : u ∈ D.core
  · rw [D.vertexLabel_core u hu] at huv
    by_cases hv : v ∈ D.core
    · rw [D.vertexLabel_core v hv] at huv
      exact coreReach hu hv (Sum.inl.inj huv)
    · rcases D.branchIndex_mem v hv with hvB | hvC
      · rw [D.vertexLabel_B _ _ hvB] at huv
        exact (coreReach hu (D.attach_mem _) (Sum.inl.inj huv)).trans (toCore v hv hvB).symm
      · rw [D.vertexLabel_C _ _ hvC] at huv
        exact Sum.noConfusion huv
  · rcases D.branchIndex_mem u hu with huB | huC
    · rw [D.vertexLabel_B _ _ huB] at huv
      by_cases hv : v ∈ D.core
      · rw [D.vertexLabel_core v hv] at huv
        exact (toCore u hu huB).trans (coreReach (D.attach_mem _) hv (Sum.inl.inj huv))
      · rcases D.branchIndex_mem v hv with hvB | hvC
        · rw [D.vertexLabel_B _ _ hvB] at huv
          exact (toCore u hu huB).trans ((coreReach (D.attach_mem _) (D.attach_mem _)
            (Sum.inl.inj huv)).trans (toCore v hv hvB).symm)
        · rw [D.vertexLabel_C _ _ hvC] at huv
          exact Sum.noConfusion huv
    · rw [D.vertexLabel_C _ _ huC] at huv
      by_cases hv : v ∈ D.core
      · rw [D.vertexLabel_core v hv] at huv
        exact Sum.noConfusion huv
      · rcases D.branchIndex_mem v hv with hvB | hvC
        · rw [D.vertexLabel_B _ _ hvB] at huv
          exact Sum.noConfusion huv
        · rw [D.vertexLabel_C _ _ hvC] at huv
          have hi := Sum.inr.inj huv
          exact tipReach _ huC (hi.symm ▸ hvC)

/-- Actual post-component incidence follows from constructed labels. No post
component classification or endpoint incidence is a premise. -/
theorem fullEndpoint_component_card_bound {J : Type*} [Finite I] [Finite J]
    (D : BranchAttachmentData V I old post) (root : J → V)
    (hroot : ∀ j, root j ∈ D.core) (K : ℕ) (hK : 1 ≤ K)
    (hrootcount : ∀ c, Nat.card {j : J // D.rootLabel root hroot j = c} ≤ K)
    (hattachcount : ∀ c, Nat.card {i : I // D.centralLabel i = c} ≤ K)
    (c : post.ConnectedComponent) :
    Nat.card {p : J ⊕ (I × Fin 2) // D.fullEndpoint root p ∈ c.supp} ≤ 2*K := by
  classical
  by_cases hn : Nonempty {p : J ⊕ (I × Fin 2) // D.fullEndpoint root p ∈ c.supp}
  · let p := Classical.choice hn
    let label := D.vertexLabel (D.fullEndpoint root p.val)
    have hlabel (q : {p : J ⊕ (I × Fin 2) // D.fullEndpoint root p ∈ c.supp}) :
        D.vertexLabel (D.fullEndpoint root q.val) = label := by
      exact D.vertexLabel_eq_of_reachable (SimpleGraph.ConnectedComponent.exact
        (q.property.trans p.property.symm))
    have hle := Nat.card_le_card_of_injective
      (fun q : {p : J ⊕ (I × Fin 2) // D.fullEndpoint root p ∈ c.supp} =>
        (⟨q.val,hlabel q⟩ : {q : J ⊕ (I × Fin 2) // D.vertexLabel (D.fullEndpoint root q) = label}))
      (by
        intro x y h
        apply Subtype.ext
        exact congrArg (fun z : {q : J ⊕ (I × Fin 2) // D.vertexLabel (D.fullEndpoint root q) = label} => z.val) h)
    cases hl : label with
    | inl cc =>
      rw [hl, D.centralEndpointFiber_card root hroot cc] at hle
      exact hle.trans (by have h₁ := hrootcount cc; have h₂ := hattachcount cc; omega)
    | inr i =>
      rw [hl] at hle
      exact hle.trans ((D.detachedEndpointFiber_card_le_one root hroot i).trans (by omega))
  · have he : IsEmpty {p : J ⊕ (I × Fin 2) // D.fullEndpoint root p ∈ c.supp} := not_nonempty_iff.mp hn
    letI := he
    exact (Nat.card_of_isEmpty).le.trans (Nat.zero_le _)

end BranchAttachmentData
end LocalLaw
