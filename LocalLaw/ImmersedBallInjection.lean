import LocalLaw.ImmersionForest

/-! # A locally injective map is injective inside a forest ball -/

noncomputable section
namespace LocalLaw
variable {V W : Type*}{G : SimpleGraph V}{H : SimpleGraph W}

theorem immersed_ball_injective (f : G→gH)(hloc : GraphHomLocallyInjective f)
    (x : V)(r R : ℕ)
    (himage : ∀v ∈ graphBallVertices G x r,f v ∈ graphBallVertices H (f x) R)
    (htree : (graphBall H (f x) R).IsTree) :
    Function.Injective (fun v : graphBallVertices G x r => f v.val) := by
  let F : graphBall G x r →g graphBall H (f x) R :=
    {toFun := fun v => ⟨f v.val,himage v.val v.property⟩
     map_rel' := fun h => f.map_rel h}
  have hF : GraphHomLocallyInjective F := by
    intro a b c hab hac h
    exact Subtype.ext (hloc a.val b.val c.val hab hac (congrArg Subtype.val h))
  intro a b he
  have he' : F a=F b := Subtype.ext he
  obtain ⟨p,hp⟩ := (graphBall_connected G x r).exists_isPath a b
  have hm := map_path_into_forest F hF htree.IsAcyclic p hp
  cases p with
  | nil => rfl
  | @cons a c b h p =>
    change ((p.map F).cons (F.map_rel h)).IsPath at hm
    have hn := ((SimpleGraph.Walk.cons_isPath_iff _ _).mp hm).2
    apply False.elim
    apply hn
    rw [he']
    exact (p.map F).end_mem_support

end LocalLaw
