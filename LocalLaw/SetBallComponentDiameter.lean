import LocalLaw.FiniteBallCover
import LocalLaw.ComponentBallGeometry
import LocalLaw.GraphMetricLocality

/-!
# Intrinsic set-ball diameter from its actual component root count

The general finite ball-cover theorem is applied through an explicit graph
isomorphism. Only the number of roots in the same actual component matters;
arbitrarily many other sampled patches do not enlarge this diameter.
-/

noncomputable section
namespace LocalLaw
local instance setBallComponentDiameterDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type} [Fintype V]

def setBallRoot (G : SimpleGraph V) (roots : Set V) (r : ℕ) (a : roots) :
    graphSetBall G roots r := ⟨a.val, a.val, a.property, by simp⟩

def setBallCoverIso (G : SimpleGraph V) (roots : Set V) (r : ℕ) :
    (G.induce (graphSetBall G roots r)) ≃g
      ballCoverGraph G (Subtype.val : roots → V) (fun _ => r) where
  toEquiv :=
    { toFun := fun v => ⟨v.val, by obtain ⟨u, hu, hd⟩ := v.property; exact ⟨⟨u, hu⟩, hd⟩⟩
      invFun := fun v => ⟨v.val, by obtain ⟨u, hd⟩ := v.property; exact ⟨u.val, u.property, hd⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  map_rel_iff' := Iff.rfl

/-- The actual root fiber controls the actual intrinsic diameter, also for
disconnected set-ball unions. -/
theorem setBall_distance_bound_of_component_root_count (G : SimpleGraph V)
    (roots : Set V) (r m : ℕ) (hm : 1 ≤ m)
    (hroots : ∀ c : (G.induce (graphSetBall G roots r)).ConnectedComponent,
      Nat.card {a : roots // setBallRoot G roots r a ∈ c.supp} ≤ m)
    (x y : graphSetBall G roots r) :
    (G.induce (graphSetBall G roots r)).dist x y ≤ m * (2 * r + 1) := by
  let H := G.induce (graphSetBall G roots r)
  let e := setBallCoverIso G roots r
  let center : roots → V := Subtype.val
  let radius : roots → ℕ := fun _ => r
  have hcover : ∀ c : (ballCoverGraph G center radius).ConnectedComponent,
      Nat.card {a : roots // ballCoverCenter G center radius a ∈ c.supp} ≤ m := by
    intro c
    let v : c.supp := Classical.choice c.connected_induce_supp.nonempty
    let ca := H.connectedComponentMk (e.symm v.val)
    let f : {a : roots // ballCoverCenter G center radius a ∈ c.supp} →
        {a : roots // setBallRoot G roots r a ∈ ca.supp} := fun a => ⟨a.val, by
      obtain ⟨p⟩ := c.connected_induce_supp.preconnected v ⟨ballCoverCenter G center radius a.val, a.property⟩
      let q := (p.map (SimpleGraph.Embedding.induce c.supp).toHom).map e.symm.toHom
      exact (SimpleGraph.ConnectedComponent.sound q.reachable).symm⟩
    have hf : Function.Injective f := by
      intro a b hab
      have hv : a.val = b.val := congrArg
        (fun z : {a : roots // setBallRoot G roots r a ∈ ca.supp} => z.val) hab
      exact Subtype.ext hv
    exact (Nat.card_le_card_of_injective f hf).trans (hroots ca)
  have hh := ballCover_distance_bound_of_component_root_count G center radius r
    (fun _ => le_rfl) m hcover (e x) (e y)
  rw [graphIso_dist e] at hh
  change H.dist x y ≤ _ at hh
  have hnat : 2 * r + (m - 1) * (2 * r + 1) ≤ m * (2 * r + 1) := by
    have hmEq : m - 1 + 1 = m := Nat.sub_add_cancel hm
    calc
      _ ≤ (2 * r + 1) + (m - 1) * (2 * r + 1) := Nat.add_le_add_right (Nat.le_succ _) _
      _ = (m - 1 + 1) * (2 * r + 1) := by ring
      _ = _ := by rw [hmEq]
  exact hh.trans hnat

/-- The same diameter statement on any literally equal common vertex set,
with any proof-irrelevant embedding of its actual roots. -/
theorem setBall_restriction_distance_bound (G : SimpleGraph V) (S roots : Set V)
    (r m : ℕ) (hm : 1 ≤ m) (hS : S = graphSetBall G roots r) (e : roots ↪ S)
    (he : ∀ a, (e a).val = a.val)
    (hroots : ∀ c : (G.induce S).ConnectedComponent,
      Nat.card {a : roots // e a ∈ c.supp} ≤ m) (x y : S) :
    (G.induce S).dist x y ≤ m * (2 * r + 1) := by
  subst S
  have heq : ∀ a, e a = setBallRoot G roots r a := fun a => Subtype.ext (he a)
  simp_rw [heq] at hroots
  exact setBall_distance_bound_of_component_root_count G roots r m hm hroots x y

end LocalLaw
