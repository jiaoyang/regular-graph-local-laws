import SpectralConsequences.OldParentTerminal
import LocalLaw.DisconnectedEvenTransfer

/-! Connected even generators are localized in one old radius-R ball by
cutting exactly the changed parent edges. -/
noncomputable section
set_option maxHeartbeats 1800000
namespace SpectralConsequences
open LocalLaw
local instance parentEvenLocalizationDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace ParentCut
variable {U V:Type*}[Fintype U][Fintype V]

omit [Fintype U] [Fintype V] in
theorem connected_support_old_ball (D:HeightParentData U)(G:SimpleGraph V)(f:U→V)
    (R:ℕ)(hheight:∀v,D.height v≤R)(S:Set U)
    (hconn:(D.tree.induce S).Connected)
    (hOld:∀x∈S,∀y∈S,D.tree.Adj x y→G.Adj (f x) (f y))
    (v:U)(hv:v∈S):
    ∀w∈S,f w∈graphBallVertices G (f (terminal D G f v)) R:=by
  intro w hw
  have heq:=terminal_eq_on_connected D G f S hconn hOld v hv w hw
  change G.edist (f (terminal D G f v)) (f w)≤(R:ℕ∞)
  rw [heq]
  exact old_distance_to_terminal D G f R hheight w

theorem even_eq_bot_of_map_forest (F:SimpleGraph U)(f:U↪V)(G:SimpleGraph V)
    (W:Set V)(hFG:F.map f≤G)(heven:∀v,Even (F.degree v))
    (hsupport:(F.map f).support⊆W)(hforest:(G.induce W).IsAcyclic):F=⊥:=by
  let inc:W↪V:=⟨Subtype.val,Subtype.val_injective⟩
  have hs:(F.map f).support⊆Set.range inc:=fun x hx=>⟨⟨x,hsupport hx⟩,rfl⟩
  have hle:(F.map f).comap inc≤G.induce W:=fun _ _ h=>hFG h
  have hEvenCanonical:∀v,Even (Nat.card ((F.map f).neighborSet v)):=by
    simpa only [←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
      mapped_even_pattern F f heven
  have hzero:=even_pattern_eq_bot_of_comap_forest (F.map f) inc hs
    (fun v=>by simpa only [←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
      hEvenCanonical v) (graph_acyclic_of_le hle hforest)
  apply SimpleGraph.map_injective f
  rw [hzero]
  ext x y
  simp only [SimpleGraph.map_adj,SimpleGraph.bot_adj,false_and,exists_false]

theorem connected_even_eq_bot_of_terminal_ball_forest (D:HeightParentData U)
    (G:SimpleGraph V)(f:U↪V)(R:ℕ)(hheight:∀v,D.height v≤R)
    (F:SimpleGraph U)(hconn:(D.tree.induce F.support).Connected)
    (hOld:∀x∈F.support,∀y∈F.support,D.tree.Adj x y→G.Adj (f x) (f y))
    (hFG:F.map f≤G)(heven:∀v,Even (F.degree v))(v:U)(hv:v∈F.support)
    (hforest:(graphBall G (f (terminal D G f v)) R).IsAcyclic):F=⊥:=by
  apply even_eq_bot_of_map_forest F f G _ hFG heven ?_ hforest
  intro x hx
  obtain ⟨y,hxy⟩:=((F.map f).mem_support).mp hx
  obtain ⟨a,b,hab,rfl,rfl⟩:=(SimpleGraph.map_adj f F x y).mp hxy
  exact connected_support_old_ball D G f R hheight F.support hconn hOld v hv a
    ((F.mem_support).mpr ⟨b,hab⟩)

end ParentCut
end SpectralConsequences
