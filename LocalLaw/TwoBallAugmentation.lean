import LocalLaw.TwoHubMetric
import LocalLaw.FiniteBallCover

/-! Two actual graph balls added to an arbitrary old neighborhood. -/
noncomputable section
namespace LocalLaw
local instance twoBallAugmentationDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V W : Type}

def twoBallAugment (G : SimpleGraph V) (K : Set V) (x y : V) (r : ℕ) : Set V :=
  twoHubVertices K (graphBallVertices G x r) (graphBallVertices G y r)

def twoBallLeft (G : SimpleGraph V) (K : Set V) (x y : V) (r : ℕ) : twoBallAugment G K x y r :=
  ⟨x, Or.inr (Or.inl (center_mem_graphBall G x r))⟩

def twoBallRight (G : SimpleGraph V) (K : Set V) (x y : V) (r : ℕ) : twoBallAugment G K x y r :=
  ⟨y, Or.inr (Or.inr (center_mem_graphBall G y r))⟩

theorem twoBall_left_radial (G : SimpleGraph V) (K : Set V) (x y : V) (r : ℕ)
    (H : SimpleGraph W) (f : (G.induce (twoBallAugment G K x y r)) →g H)
    (v : twoBallAugment G K x y r) (hv : v.val ∈ graphBallVertices G x r) :
    H.edist (f (twoBallLeft G K x y r)) (f v) ≤ (r : ℕ∞) ∧
      (G.induce (twoBallAugment G K x y r)).Reachable v (twoBallLeft G K x y r) := by
  obtain ⟨p,hp⟩ := graphBall_walk_from_center G x r ⟨v.val,hv⟩
  let incl : graphBall G x r →g G.induce (twoBallAugment G K x y r) :=
    { toFun := fun a => ⟨a.val, Or.inr (Or.inl a.property)⟩
      map_rel' := fun h => h }
  have hd := (SimpleGraph.edist_le ((p.map incl).map f)).trans (ENat.coe_le_coe.mpr (by simpa using hp))
  exact ⟨hd,(p.map incl).reverse.reachable⟩

theorem twoBall_right_radial (G : SimpleGraph V) (K : Set V) (x y : V) (r : ℕ)
    (H : SimpleGraph W) (f : (G.induce (twoBallAugment G K x y r)) →g H)
    (v : twoBallAugment G K x y r) (hv : v.val ∈ graphBallVertices G y r) :
    H.edist (f (twoBallRight G K x y r)) (f v) ≤ (r : ℕ∞) ∧
      (G.induce (twoBallAugment G K x y r)).Reachable v (twoBallRight G K x y r) := by
  obtain ⟨p,hp⟩ := graphBall_walk_from_center G y r ⟨v.val,hv⟩
  let incl : graphBall G y r →g G.induce (twoBallAugment G K x y r) :=
    { toFun := fun a => ⟨a.val, Or.inr (Or.inr a.property)⟩
      map_rel' := fun h => h }
  have hd := (SimpleGraph.edist_le ((p.map incl).map f)).trans (ENat.coe_le_coe.mpr (by simpa using hp))
  exact ⟨hd,(p.map incl).reverse.reachable⟩

/-- Intrinsic old component bounds transfer by an actual inclusion. -/
theorem twoBall_old_intrinsic_bound (G : SimpleGraph V) (K : Set V) (x y : V) (r D : ℕ)
    (hD : ∀ u v : K, (G.induce K).dist u v ≤ D)
    (c : (G.induce K).ConnectedComponent) (u v : twoBallAugment G K x y r)
    (hu : u.val ∈ liftedComponent G K c) (hv : v.val ∈ liftedComponent G K c) :
    (G.induce (twoBallAugment G K x y r)).edist u v ≤ (D : ℕ∞) := by
  obtain ⟨huK,huc⟩ := hu
  obtain ⟨hvK,hvc⟩ := hv
  let a : K := ⟨u.val,huK⟩
  let b : K := ⟨v.val,hvK⟩
  have hr : (G.induce K).Reachable a b := SimpleGraph.ConnectedComponent.exact (huc.trans hvc.symm)
  have heq : ((G.induce K).dist a b : ℕ∞) = (G.induce K).edist a b :=
    ENat.coe_toNat (SimpleGraph.edist_ne_top_iff_reachable.mpr hr)
  let incl : (G.induce K) →g G.induce (twoBallAugment G K x y r) :=
    { toFun := fun a => ⟨a.val,Or.inl a.property⟩
      map_rel' := fun h => h }
  exact (graphHom_edist_le incl a b).trans (heq.symm.le.trans (ENat.coe_le_coe.mpr (hD a b)))

/-- The full augmented intrinsic diameter depends on at most three old
component segments and the two genuine hub balls. -/
theorem twoBallAugment_distance_bound (G : SimpleGraph V) (K : Set V) (x y : V) (r D : ℕ)
    (hD : ∀ u v : K, (G.induce K).dist u v ≤ D)
    (a b : twoBallAugment G K x y r) :
    (G.induce (twoBallAugment G K x y r)).dist a b ≤ 3*D+4*r+4 := by
  by_cases hr : (G.induce (twoBallAugment G K x y r)).Reachable a b
  · have hh := twoHub_reachable_edist_bound G K (graphBallVertices G x r) (graphBallVertices G y r)
      (G.induce (twoBallAugment G K x y r)) (SimpleGraph.Hom.id : (G.induce (twoBallAugment G K x y r)) →g (G.induce (twoBallAugment G K x y r)))
      (twoBallLeft G K x y r) (twoBallRight G K x y r)
      (center_mem_graphBall G x r) (center_mem_graphBall G y r) D r
      (twoBall_old_intrinsic_bound G K x y r D hD)
      (twoBall_left_radial G K x y r _ (SimpleGraph.Hom.id : (G.induce (twoBallAugment G K x y r)) →g (G.induce (twoBallAugment G K x y r))))
      (twoBall_right_radial G K x y r _ (SimpleGraph.Hom.id : (G.induce (twoBallAugment G K x y r)) →g (G.induce (twoBallAugment G K x y r)))) a b hr
    have heq : ((G.induce (twoBallAugment G K x y r)).dist a b : ℕ∞) =
        (G.induce (twoBallAugment G K x y r)).edist a b :=
      ENat.coe_toNat (SimpleGraph.edist_ne_top_iff_reachable.mpr hr)
    exact ENat.coe_le_coe.mp (heq.le.trans hh)
  · rw [SimpleGraph.dist_eq_zero_of_not_reachable hr]
    exact Nat.zero_le _

end LocalLaw
