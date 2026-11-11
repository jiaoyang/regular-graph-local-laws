import LocalLaw.BallCycleWitness

/-! # Cutting a rooted BFS tree at precisely its changed parent edges

The terminal and the old-graph walks are constructed from parent data.
No component label or old-ball localization is an input.
-/

open Set
noncomputable section
namespace SpectralConsequences
open LocalLaw
local instance oldParentTerminalDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace ParentCut
variable {U V : Type*}

theorem root_path (D : HeightParentData U) (v : U) :
    ∃ p : D.tree.Walk v D.root, p.IsPath ∧ p.length=D.height v ∧
      ∀w ∈ p.support,D.height w ≤ D.height v := by
  have haux : ∀n : ℕ,∀w : U,D.height w=n →
      ∃ p : D.tree.Walk w D.root,p.IsPath ∧ p.length=D.height w ∧
        ∀z ∈ p.support,D.height z ≤ D.height w := by
    intro n
    induction n with
    | zero =>
      intro w hw
      have heq := (D.height_zero w).mp hw
      subst w
      refine ⟨SimpleGraph.Walk.nil,by simp,by simp [hw],?_⟩
      intro z hz
      have heq : z=D.root := by simpa only [SimpleGraph.Walk.support_nil,List.mem_singleton] using hz
      rw [heq]
    | succ n ih =>
      intro w hw
      have hwr : w ≠ D.root := by
        intro heq
        have hz := (D.height_zero w).mpr heq
        omega
      let u := D.parent ⟨w,hwr⟩
      have hu : D.height u=n := by
        have hp := D.parent_height ⟨w,hwr⟩
        change D.height u+1=D.height w at hp
        omega
      obtain ⟨p,hp,hlen,hheight⟩ := ih u hu
      have hw_not : w ∉ p.support := by
        intro hmem
        have hh := hheight w hmem
        omega
      refine ⟨p.cons (D.parent_adj ⟨w,hwr⟩),hp.cons hw_not,?_,?_⟩
      · simp only [SimpleGraph.Walk.length_cons,hlen]
        exact D.parent_height ⟨w,hwr⟩
      · intro z hz
        simp only [SimpleGraph.Walk.support_cons,List.mem_cons] at hz
        rcases hz with rfl|hz
        · exact le_rfl
        · have hh := hheight z hz
          omega
  exact haux (D.height v) v rfl

def terminal (D : HeightParentData U) (G : SimpleGraph V) (f : U → V) (v : U) : U :=
  if hv : v=D.root then v
  else if G.Adj (f v) (f (D.parent ⟨v,hv⟩)) then
    terminal D G f (D.parent ⟨v,hv⟩)
  else v
termination_by D.height v
decreasing_by
  have hh := D.parent_height ⟨v,hv⟩
  change D.height (D.parent ⟨v,hv⟩)+1=D.height v at hh
  omega

theorem terminal_of_root (D : HeightParentData U) (G : SimpleGraph V) (f : U → V) :
    terminal D G f D.root=D.root := by rw [terminal,dif_pos rfl]

theorem terminal_parent (D : HeightParentData U) (G : SimpleGraph V) (f : U → V)
    (v : U) (hv : v ≠ D.root) (hOld : G.Adj (f v) (f (D.parent ⟨v,hv⟩))) :
    terminal D G f v=terminal D G f (D.parent ⟨v,hv⟩) := by
  rw [terminal,dif_neg hv,if_pos hOld]

theorem root_path_before_parent (D : HeightParentData U) (v : U) (hv : v ≠ D.root) :
    ∃ p : D.tree.Walk D.root (D.parent ⟨v,hv⟩),
      (p.concat (D.parent_adj ⟨v,hv⟩).symm).IsPath ∧
      p.length+1=D.height v := by
  obtain ⟨q,hq,hlen,hheight⟩ := root_path D (D.parent ⟨v,hv⟩)
  have hparent := D.parent_height ⟨v,hv⟩
  change D.height (D.parent ⟨v,hv⟩)+1=D.height v at hparent
  have hnot : v ∉ q.support := by
    intro hm
    have hh := hheight v hm
    omega
  refine ⟨q.reverse,?_,?_⟩
  · have hp : (q.cons (D.parent_adj ⟨v,hv⟩)).reverse.IsPath := (hq.cons hnot).reverse
    simpa only [SimpleGraph.Walk.reverse_cons] using hp
  · simpa only [SimpleGraph.Walk.length_reverse,hlen] using hparent

theorem mapped_root_path_before_parent (D:HeightParentData U)(H:SimpleGraph V)
    (f:D.tree→g H)(hf:Function.Injective f)(v:U)(hv:v≠D.root)
    (a b:V)(ha:f v=a)(hb:f (D.parent ⟨v,hv⟩)=b):
    ∃p:H.Walk (f D.root) b,∃hab:H.Adj b a,
      (p.concat hab).IsPath ∧p.length+1=D.height v:=by
  subst a
  subst b
  obtain ⟨p,hp,hlen⟩:=root_path_before_parent D v hv
  refine ⟨p.map f,f.map_rel (D.parent_adj ⟨v,hv⟩).symm,?_,?_⟩
  · have hm:((p.concat (D.parent_adj ⟨v,hv⟩).symm).map f).IsPath:=
      SimpleGraph.Walk.map_isPath_of_injective hf hp
    simpa only [SimpleGraph.Walk.concat_eq_append,SimpleGraph.Walk.map_append,
      SimpleGraph.Walk.map_cons,SimpleGraph.Walk.map_nil] using hm
  · simpa only [SimpleGraph.Walk.length_map] using hlen

theorem terminal_stop (D : HeightParentData U) (G : SimpleGraph V) (f : U → V) (v : U) :
    terminal D G f v=D.root ∨
      ∃ h : terminal D G f v ≠ D.root,
        ¬G.Adj (f (terminal D G f v)) (f (D.parent ⟨terminal D G f v,h⟩)) := by
  have haux : ∀n : ℕ,∀w : U,D.height w=n →
      terminal D G f w=D.root ∨ ∃h : terminal D G f w ≠ D.root,
        ¬G.Adj (f (terminal D G f w)) (f (D.parent ⟨terminal D G f w,h⟩)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro w hw
      by_cases hwr : w=D.root
      · subst w
        exact Or.inl (terminal_of_root D G f)
      by_cases hOld : G.Adj (f w) (f (D.parent ⟨w,hwr⟩))
      · rw [terminal_parent D G f w hwr hOld]
        apply ih (D.height (D.parent ⟨w,hwr⟩)) _ _ rfl
        have hh := D.parent_height ⟨w,hwr⟩
        change D.height (D.parent ⟨w,hwr⟩)+1=D.height w at hh
        omega
      · rw [terminal,dif_neg hwr,if_neg hOld]
        exact Or.inr ⟨hwr,hOld⟩
  exact haux (D.height v) v rfl

theorem old_walk_to_terminal (D : HeightParentData U) (G : SimpleGraph V) (f : U → V) (v : U) :
    ∃p : G.Walk (f v) (f (terminal D G f v)),p.length+D.height (terminal D G f v)=D.height v := by
  have haux : ∀n : ℕ,∀w : U,D.height w=n →
      ∃p : G.Walk (f w) (f (terminal D G f w)),
        p.length+D.height (terminal D G f w)=D.height w := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro w hw
      by_cases hwr : w=D.root
      · subst w
        rw [terminal_of_root]
        exact ⟨SimpleGraph.Walk.nil,by simp⟩
      by_cases hOld : G.Adj (f w) (f (D.parent ⟨w,hwr⟩))
      · rw [terminal_parent D G f w hwr hOld]
        have hparent := D.parent_height ⟨w,hwr⟩
        change D.height (D.parent ⟨w,hwr⟩)+1=D.height w at hparent
        obtain ⟨p,hp⟩ := ih (D.height (D.parent ⟨w,hwr⟩)) (by omega) _ rfl
        refine ⟨p.cons hOld,?_⟩
        simp only [SimpleGraph.Walk.length_cons]
        omega
      · rw [terminal,dif_neg hwr,if_neg hOld]
        exact ⟨SimpleGraph.Walk.nil,by simp⟩
  exact haux (D.height v) v rfl

theorem terminal_adj (D : HeightParentData U) (G : SimpleGraph V) (f : U → V)
    {x y : U} (hxy : D.tree.Adj x y) (hOld : G.Adj (f x) (f y)) :
    terminal D G f x=terminal D G f y := by
  obtain ⟨⟨v,hv⟩,_⟩ := (SimpleGraph.fromEdgeSet_adj (Set.range D.parentEdge)).mp hxy
  change s(v.val,D.parent v)=s(x,y) at hv
  rcases Sym2.eq_iff.mp hv with ⟨hx,hy⟩|⟨hy,hx⟩
  · rw [←hx,←hy] at hOld ⊢
    exact terminal_parent D G f v.val v.property hOld
  · rw [←hx,←hy] at hOld ⊢
    exact (terminal_parent D G f v.val v.property hOld.symm).symm

theorem terminal_eq_on_connected (D : HeightParentData U) (G : SimpleGraph V) (f : U → V)
    (S : Set U) (hconn : (D.tree.induce S).Connected)
    (hOld : ∀x ∈ S,∀y ∈ S,D.tree.Adj x y → G.Adj (f x) (f y)) :
    ∀x ∈ S,∀y ∈ S,terminal D G f x=terminal D G f y := by
  intro x hx y hy
  obtain ⟨p⟩ := hconn ⟨x,hx⟩ ⟨y,hy⟩
  have haux : ∀{u v : S},(D.tree.induce S).Walk u v → terminal D G f u.val=terminal D G f v.val := by
    intro u v q
    induction q with
    | nil => rfl
    | @cons u v w huv q ih =>
      exact (terminal_adj D G f huv (hOld u.val u.property v.val v.property huv)).trans ih
  exact haux p

theorem old_distance_to_terminal (D : HeightParentData U) (G : SimpleGraph V) (f : U → V)
    (R : ℕ) (hheight : ∀v,D.height v ≤ R) (v : U) :
    G.edist (f (terminal D G f v)) (f v) ≤ (R : ℕ∞) := by
  obtain ⟨p,hp⟩ := old_walk_to_terminal D G f v
  exact (G.edist_le p.reverse).trans (ENat.coe_le_coe.mpr (by
    simp only [SimpleGraph.Walk.length_reverse]
    have hv := hheight v
    omega))

end ParentCut
end SpectralConsequences
