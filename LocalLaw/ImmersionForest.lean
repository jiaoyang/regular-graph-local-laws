import LocalLaw.TreeReferenceKernel
import LocalLaw.CapturedBallComponents

/-! # Locally injective graph maps into forests

A graph map that is injective on each neighbor set cannot create a cycle
inside a tree patch. Global injectivity is unnecessary: distinct artificial
leaves may have the same original label outside the selected patch.
-/

namespace LocalLaw
variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

def GraphHomLocallyInjective (f : G→gH) : Prop :=
  ∀ a b c,G.Adj a b→G.Adj a c→f b=f c→b=c

theorem map_path_into_forest (f : G→gH) (hloc : GraphHomLocallyInjective f)
    (hforest : H.IsAcyclic) {a b : V} (p : G.Walk a b) (hp : p.IsPath) :
    (p.map f).IsPath := by
  classical
  induction p with
  | nil => simp
  | @cons u a b hua p ih =>
    have hpath : p.IsPath := hp.of_cons
    have hnot : u∉p.support := ((SimpleGraph.Walk.cons_isPath_iff _ _).mp hp).2
    have hmap := ih hpath
    change ((p.map f).cons (f.map_rel hua)).IsPath
    apply hmap.cons
    intro hmem
    have hfa : f a≠f u := (f.map_rel hua).ne.symm
    have htake := hmap.takeUntil hmem
    have heq := congrArg Subtype.val (hforest.path_unique ⟨(p.map f).takeUntil (f u) hmem,htake⟩
      (SimpleGraph.Path.singleton (f.map_rel hua).symm))
    cases p with
    | nil =>
      simp only [SimpleGraph.Walk.map_nil,SimpleGraph.Walk.support_nil,List.mem_singleton] at hmem
      exact hfa hmem.symm
    | @cons a w b haw rest =>
      have hrest : f u∈(rest.map f).support := by
        simpa only [SimpleGraph.Walk.map_cons,SimpleGraph.Walk.support_cons,List.mem_cons,
          show ¬f u=f a from Ne.symm hfa,false_or] using hmem
      simp only [SimpleGraph.Walk.map_cons] at heq
      rw [SimpleGraph.Walk.takeUntil_cons hrest hfa] at heq
      have hv:=congrArg (fun q : H.Walk (f a) (f u)=>q.getVert 1) heq
      simp only [SimpleGraph.Path.singleton,SimpleGraph.Walk.getVert_cons_succ,SimpleGraph.Walk.getVert_zero] at hv
      have huw : u=w := hloc a u w hua.symm haw hv.symm
      have hw : w∈(rest.cons haw).support := by
        rw [SimpleGraph.Walk.support_cons,List.mem_cons]
        exact Or.inr rest.start_mem_support
      exact hnot (huw.symm ▸ hw)

theorem acyclic_of_locally_injective_hom (f : G→gH) (hloc : GraphHomLocallyInjective f)
    (hforest : H.IsAcyclic) : G.IsAcyclic := by
  intro a p hp
  cases p with
  | nil => exact hp.not_of_nil
  | @cons a b a hab tail =>
    have htail : tail.IsPath := (SimpleGraph.Walk.cons_isCycle_iff _ _).mp hp |>.1
    have hmap := map_path_into_forest f hloc hforest tail htail
    have heq := congrArg Subtype.val (hforest.path_unique ⟨tail.map f,hmap⟩
      (SimpleGraph.Path.singleton (f.map_rel hab).symm))
    have hlen:=congrArg SimpleGraph.Walk.length heq
    simp only [SimpleGraph.Path.singleton,SimpleGraph.Walk.length_map,SimpleGraph.Walk.length_cons,
      SimpleGraph.Walk.length_nil] at hlen
    have hthree:=hp.three_le_length
    simp only [SimpleGraph.Walk.length_cons] at hthree
    omega


theorem graphBall_tree_of_locally_injective_hom (f : G→gH) (hloc : GraphHomLocallyInjective f)
    (root : V) (r R : ℕ)
    (himage : ∀ v∈graphBallVertices G root r,f v∈graphBallVertices H (f root) R)
    (htree : (graphBall H (f root) R).IsTree) : (graphBall G root r).IsTree := by
  let F : graphBall G root r →g graphBall H (f root) R :=
    { toFun:=fun v=>⟨f v.val,himage v.val v.property⟩
      map_rel':=fun h=>f.map_rel h }
  have hF : GraphHomLocallyInjective F := by
    intro a b c hab hac he
    apply Subtype.ext
    exact hloc a.val b.val c.val hab hac (congrArg Subtype.val he)
  exact ⟨graphBall_connected G root r,acyclic_of_locally_injective_hom F hF htree.IsAcyclic⟩

end LocalLaw
