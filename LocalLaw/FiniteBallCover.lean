import LocalLaw.TreeRadiusStability
import LocalLaw.ComponentBallGeometry

/-!
# Intrinsic geometry of an actual finite union of balls

An auxiliary graph records genuine crossing edges between covering balls.
Walks in the induced union give auxiliary reachability; simple auxiliary
paths lift back to short walks in the actual induced graph. This also gives
the sharper bound in terms of the number of ball centers in one component.
-/

noncomputable section
namespace LocalLaw
local instance finiteBallCoverDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V I : Type*}

def ballCoverVertices (G : SimpleGraph V) (center : I → V) (radius : I → ℕ) : Set V :=
  {v | ∃ a, v ∈ graphBallVertices G (center a) (radius a)}

abbrev ballCoverGraph (G : SimpleGraph V) (center : I → V) (radius : I → ℕ) :=
  G.induce (ballCoverVertices G center radius)

def ballCoverCenter (G : SimpleGraph V) (center : I → V) (radius : I → ℕ) (a : I) :
    ballCoverVertices G center radius := ⟨center a, a, center_mem_graphBall G _ _⟩

def ballCoverLabel (G : SimpleGraph V) (center : I → V) (radius : I → ℕ)
    (v : ballCoverVertices G center radius) : I := Classical.choose v.property

theorem ballCoverLabel_mem (G : SimpleGraph V) (center : I → V) (radius : I → ℕ)
    (v : ballCoverVertices G center radius) :
    v.val ∈ graphBallVertices G (center (ballCoverLabel G center radius v))
      (radius (ballCoverLabel G center radius v)) := Classical.choose_spec v.property

def ballCoverBallHom (G : SimpleGraph V) (center : I → V) (radius : I → ℕ) (a : I) :
    graphBall G (center a) (radius a) →g ballCoverGraph G center radius where
  toFun v := ⟨v.val, a, v.property⟩
  map_rel' := fun h => h

/-- A root-to-vertex walk stays in the induced ball and has its actual
ambient distance length, in particular no greater than the radius. -/
theorem graphBall_walk_from_center (G : SimpleGraph V) (o : V) (r : ℕ)
    (v : graphBallVertices G o r) :
    ∃ p : (graphBall G o r).Walk ⟨o, center_mem_graphBall G o r⟩ v, p.length ≤ r := by
  let D := ballHeightParentData G o r
  have hle : D.tree ≤ graphBall G o r := D.tree_le _ (ballHeightParentData_parent_adj G o r)
  obtain ⟨p, hp⟩ := D.walk_to_root v
  refine ⟨(p.mapLe hle).reverse, ?_⟩
  simpa only [SimpleGraph.Walk.length_reverse, SimpleGraph.Walk.mapLe,
    SimpleGraph.Walk.length_map, hp] using ballVertexHeight_le G o r v

def ballCoverAux (G : SimpleGraph V) (center : I → V) (radius : I → ℕ) : SimpleGraph I where
  Adj a b := a ≠ b ∧ ∃ x : graphBallVertices G (center a) (radius a),
    ∃ y : graphBallVertices G (center b) (radius b), G.Adj x.val y.val
  symm := by
    intro a b
    rintro ⟨hab, x, y, hxy⟩
    exact ⟨hab.symm, y, x, hxy.symm⟩
  loopless := by intro a h; exact h.1 rfl

theorem ballCover_aux_edge_walk (G : SimpleGraph V) (center : I → V) (radius : I → ℕ)
    (s : ℕ) (hcap : ∀ a, radius a ≤ s) {a b : I}
    (hab : (ballCoverAux G center radius).Adj a b) :
    ∃ p : (ballCoverGraph G center radius).Walk
      (ballCoverCenter G center radius a) (ballCoverCenter G center radius b), p.length ≤ 2 * s + 1 := by
  obtain ⟨_, x, y, hxy⟩ := hab
  obtain ⟨pa, hpa⟩ := graphBall_walk_from_center G (center a) (radius a) x
  obtain ⟨pb, hpb⟩ := graphBall_walk_from_center G (center b) (radius b) y
  let left := pa.map (ballCoverBallHom G center radius a)
  let right := pb.map (ballCoverBallHom G center radius b)
  have hedge : (ballCoverGraph G center radius).Adj
      ((ballCoverBallHom G center radius a) x) ((ballCoverBallHom G center radius b) y) := hxy
  refine ⟨left.append (right.reverse.cons hedge), ?_⟩
  simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons,
    SimpleGraph.Walk.length_reverse, SimpleGraph.Walk.length_map, left, right]
  have ha := hcap a
  have hb := hcap b
  omega

theorem ballCover_aux_walk_lift (G : SimpleGraph V) (center : I → V) (radius : I → ℕ)
    (s : ℕ) (hcap : ∀ a, radius a ≤ s) {a b : I}
    (p : (ballCoverAux G center radius).Walk a b) :
    ∃ q : (ballCoverGraph G center radius).Walk
      (ballCoverCenter G center radius a) (ballCoverCenter G center radius b),
        q.length ≤ (2 * s + 1) * p.length := by
  induction p with
  | nil => exact ⟨SimpleGraph.Walk.nil, by simp⟩
  | @cons a b c hab p ih =>
    obtain ⟨edge, hedge⟩ := ballCover_aux_edge_walk G center radius s hcap hab
    obtain ⟨q, hq⟩ := ih
    refine ⟨edge.append q, ?_⟩
    simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons]
    nlinarith

theorem ballCover_vertex_to_center (G : SimpleGraph V) (center : I → V) (radius : I → ℕ)
    (s : ℕ) (hcap : ∀ a, radius a ≤ s) (v : ballCoverVertices G center radius) :
    ∃ p : (ballCoverGraph G center radius).Walk v
      (ballCoverCenter G center radius (ballCoverLabel G center radius v)), p.length ≤ s := by
  let a := ballCoverLabel G center radius v
  let vv : graphBallVertices G (center a) (radius a) := ⟨v.val, ballCoverLabel_mem G center radius v⟩
  obtain ⟨p, hp⟩ := graphBall_walk_from_center G (center a) (radius a) vv
  refine ⟨(p.map (ballCoverBallHom G center radius a)).reverse, ?_⟩
  simpa only [SimpleGraph.Walk.length_reverse, SimpleGraph.Walk.length_map] using hp.trans (hcap a)

theorem ballCover_walk_aux_reachable (G : SimpleGraph V) (center : I → V) (radius : I → ℕ)
    {a b : ballCoverVertices G center radius} (p : (ballCoverGraph G center radius).Walk a b) :
    (ballCoverAux G center radius).Reachable (ballCoverLabel G center radius a)
      (ballCoverLabel G center radius b) := by
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a b c hab p ih =>
    by_cases heq : ballCoverLabel G center radius a = ballCoverLabel G center radius b
    · rw [heq]
      exact ih
    · have hedge : (ballCoverAux G center radius).Adj (ballCoverLabel G center radius a)
          (ballCoverLabel G center radius b) :=
        ⟨heq, ⟨a.val, ballCoverLabel_mem G center radius a⟩,
          ⟨b.val, ballCoverLabel_mem G center radius b⟩, hab⟩
      exact hedge.reachable.trans ih

section FiniteCenters
variable [Fintype I]

/-- A component needs only its own covering centers in the diameter bound.
The graph may have arbitrarily many other covering balls. -/
theorem ballCover_distance_bound_of_component_root_count (G : SimpleGraph V)
    (center : I → V) (radius : I → ℕ) (s : ℕ) (hcap : ∀ a, radius a ≤ s)
    (κ : ℕ)
    (hroots : ∀ c : (ballCoverGraph G center radius).ConnectedComponent,
      Nat.card {a : I // ballCoverCenter G center radius a ∈ c.supp} ≤ κ)
    (a b : ballCoverVertices G center radius) :
    (ballCoverGraph G center radius).dist a b ≤ 2 * s + (κ - 1) * (2 * s + 1) := by
  by_cases hr : (ballCoverGraph G center radius).Reachable a b
  · obtain ⟨p⟩ := hr
    have haux := ballCover_walk_aux_reachable G center radius p
    obtain ⟨q, hq, _⟩ := haux.exists_path_of_dist
    obtain ⟨pa, hpa⟩ := ballCover_vertex_to_center G center radius s hcap a
    obtain ⟨pb, hpb⟩ := ballCover_vertex_to_center G center radius s hcap b
    let c := (ballCoverGraph G center radius).connectedComponentMk a
    have hroot (j : I) (hj : j ∈ q.support) : ballCoverCenter G center radius j ∈ c.supp := by
      obtain ⟨prefixWalk, _⟩ := ballCover_aux_walk_lift G center radius s hcap (q.takeUntil j hj)
      have hh := pa.reachable.trans prefixWalk.reachable
      exact (SimpleGraph.ConnectedComponent.sound hh).symm
    have hsub : q.support.toFinset ⊆ Finset.univ.filter
        (fun j : I => ballCoverCenter G center radius j ∈ c.supp) := by
      intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hroot j (List.mem_toFinset.mp hj)⟩
    have hfilter : (Finset.univ.filter
        (fun j : I => ballCoverCenter G center radius j ∈ c.supp)).card =
        Nat.card {j : I // ballCoverCenter G center radius j ∈ c.supp} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hlength : q.length + 1 ≤ κ := by
      calc
        _ = q.support.toFinset.card := by
          rw [List.toFinset_card_of_nodup hq.support_nodup, SimpleGraph.Walk.length_support]
        _ ≤ _ := Finset.card_le_card hsub
        _ = _ := hfilter
        _ ≤ κ := hroots c
    have hlength' : q.length ≤ κ - 1 := by omega
    obtain ⟨lifted, hlifted⟩ := ballCover_aux_walk_lift G center radius s hcap q
    let result := pa.append (lifted.append pb.reverse)
    have hmul := Nat.mul_le_mul_left (2 * s + 1) hlength'
    calc
      _ ≤ result.length := SimpleGraph.dist_le result
      _ ≤ 2 * s + (κ - 1) * (2 * s + 1) := by
        simp only [result, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
        nlinarith
  · rw [SimpleGraph.dist_eq_zero_of_not_reachable hr]
    exact Nat.zero_le _

/-- An m-ball union has intrinsic component diameter at most
`2*s+(m-1)*(2*s+1)`, including disconnected unions. -/
theorem ballCover_distance_bound (G : SimpleGraph V) (center : I → V) (radius : I → ℕ)
    (s : ℕ) (hcap : ∀ a, radius a ≤ s) (a b : ballCoverVertices G center radius) :
    (ballCoverGraph G center radius).dist a b ≤
      2 * s + (Fintype.card I - 1) * (2 * s + 1) := by
  apply ballCover_distance_bound_of_component_root_count G center radius s hcap (Fintype.card I) _ a b
  intro c
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_le_of_injective Subtype.val Subtype.val_injective

end FiniteCenters

def tripleBallVertices (G : SimpleGraph V) (o i j : V) (r0 r1 r2 : ℕ) : Set V :=
  ballCoverVertices G ![o, i, j] ![r0, r1, r2]

abbrev tripleBallGraph (G : SimpleGraph V) (o i j : V) (r0 r1 r2 : ℕ) :=
  G.induce (tripleBallVertices G o i j r0 r1 r2)

theorem tripleBall_distance_bound (G : SimpleGraph V) (o i j : V) (r0 r1 r2 s : ℕ)
    (h0 : r0 ≤ s) (h1 : r1 ≤ s) (h2 : r2 ≤ s)
    (a b : tripleBallVertices G o i j r0 r1 r2) :
    (tripleBallGraph G o i j r0 r1 r2).dist a b ≤ 6 * s + 2 := by
  have hh := ballCover_distance_bound G ![o, i, j] ![r0, r1, r2] s
    (by intro k; fin_cases k <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] <;> assumption)
    a b
  change (tripleBallGraph G o i j r0 r1 r2).dist a b ≤ _ at hh
  norm_num at hh
  omega

end LocalLaw
