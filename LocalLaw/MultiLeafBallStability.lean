import LocalLaw.MultiLeafAugmentation
import LocalLaw.ImmersionForest

/-! # Remote pendant attachments preserve a local tree ball

A new leaf whose mate lies outside the old radius-r ball cannot occur in
the new radius-r ball. Projection therefore gives an injective graph map
between the literal finite balls.
-/

noncomputable section
namespace LocalLaw
local instance multiLeafBallStabilityDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V I J : Type*}

def multiLeafGraph_sum_iso (G : SimpleGraph V) (a : I→V) (b : J→V) :
    multiLeafGraph G (Sum.elim a b) ≃g
      multiLeafGraph (multiLeafGraph G a) (Sum.inl ∘ b) where
  toEquiv := (Equiv.sumAssoc V I J).symm
  map_rel_iff' := by
    intro x y
    rcases x with x|x <;> rcases y with y|y
    · rfl
    · rcases y with y|y <;> simp [multiLeafGraph,Function.comp_def]
    · rcases x with x|x <;> simp [multiLeafGraph,Function.comp_def]
    · rcases x with x|x <;> rcases y with y|y <;> simp [multiLeafGraph,Function.comp_def]

theorem multiLeafGraph_ball_excludes_leaves (G : SimpleGraph V) (mate : I→V)
    (x : V) (r : ℕ) (hfar : ∀i,(r:ℕ∞) < G.edist x (mate i))
    (v : V⊕I) (hv : v ∈ graphBallVertices (multiLeafGraph G mate) (.inl x) r) :
    ∃w : V,v = .inl w := by
  cases v with
  | inl v => exact ⟨v,rfl⟩
  | inr i =>
    exact False.elim ((not_lt_of_ge ((multiLeafGraph_edist_projection G mate (.inl x) (.inr i)).trans hv)) (hfar i))

theorem multiLeafGraph_ball_tree_of_remote_mates (G : SimpleGraph V) (mate : I→V)
    (x : V) (r : ℕ) (hfar : ∀i,(r:ℕ∞) < G.edist x (mate i))
    (htree : (graphBall G x r).IsTree) :
    (graphBall (multiLeafGraph G mate) (.inl x) r).IsTree := by
  let H := multiLeafGraph G mate
  let f : graphBall H (.inl x) r →g graphBall G x r :=
    { toFun := fun v => ⟨multiLeafProjection mate v.val,
        (multiLeafGraph_edist_projection G mate (.inl x) v.val).trans v.property⟩
      map_rel' := by
        intro u v huv
        obtain ⟨u',hu⟩ := multiLeafGraph_ball_excludes_leaves G mate x r hfar u.val u.property
        obtain ⟨v',hv⟩ := multiLeafGraph_ball_excludes_leaves G mate x r hfar v.val v.property
        change G.Adj (multiLeafProjection mate u.val) (multiLeafProjection mate v.val)
        change H.Adj u.val v.val at huv
        rw [hu,hv] at huv ⊢
        exact huv }
  have hf : Function.Injective f := by
    intro u v h
    obtain ⟨u',hu⟩ := multiLeafGraph_ball_excludes_leaves G mate x r hfar u.val u.property
    obtain ⟨v',hv⟩ := multiLeafGraph_ball_excludes_leaves G mate x r hfar v.val v.property
    have hp : multiLeafProjection mate u.val = multiLeafProjection mate v.val :=
      congrArg Subtype.val h
    rw [hu,hv] at hp
    exact Subtype.ext (hu.trans ((congrArg Sum.inl hp).trans hv.symm))
  exact ⟨graphBall_connected H (.inl x) r,fun v p hp => htree.IsAcyclic (p.map f) (hp.map hf)⟩

end LocalLaw
