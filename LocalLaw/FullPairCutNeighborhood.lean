import LocalLaw.FullPairCutGeometry
import LocalLaw.EffectiveModelRadius
import LocalLaw.AdmissibleGreenBlock

/-! # Full pair neighborhoods either contain the whole inner cut or are far away

Capturing radius one about T fixes every retained inner vertex and every
inner/exterior coupling endpoint. The complementary case places both pair
roots far from every point of T, including when a root might initially
have been allowed inside T.
-/
noncomputable section
namespace LocalLaw
local instance fullPairCutNeighborhoodDecidable (p:Prop):Decidable p:=Classical.propDecidable p
variable {V:Type}

theorem inner_cut_neighborhood_subset_pair_of_near_point (G:SimpleGraph V)(o x y:V)
    (ell r m:ℕ)(hm:m+2*ell+1≤r)(t:V)(ht:t∈graphBallVertices G o ell)
    (hxt:G.edist x t≤(m:ℕ∞)) :
    graphSetBall G (graphBallVertices G o ell) 1⊆pairBallVertices G x y r:=by
  rintro v ⟨a,ha,hav⟩
  apply Or.inl
  have hto:G.edist t o≤(ell:ℕ∞):=by simpa only[SimpleGraph.edist_comm] using ht
  calc
    _≤G.edist x t+G.edist t v:=G.edist_triangle
    _≤(m:ℕ∞)+(G.edist t a+G.edist a v):=add_le_add hxt G.edist_triangle
    _≤(m:ℕ∞)+((G.edist t o+G.edist o a)+(1:ℕ∞)):=
      add_le_add_left (add_le_add G.edist_triangle hav) _
    _≤(m:ℕ∞)+(((ell:ℕ∞)+(ell:ℕ∞))+(1:ℕ∞)):=
      add_le_add_left (add_le_add_right (add_le_add hto ha) _) _
    _=((m+2*ell+1:ℕ):ℕ∞):=by push_cast;ring
    _≤(r:ℕ∞):=ENat.coe_le_coe.mpr hm

theorem pair_cut_neighborhood_or_roots_far (G:SimpleGraph V)(o x y:V)
    (ell r m:ℕ)(hm:m+2*ell+1≤r) :
    graphSetBall G (graphBallVertices G o ell) 1⊆pairBallVertices G x y r ∨
      ∀t∈graphBallVertices G o ell,(m:ℕ∞)<G.edist x t ∧ (m:ℕ∞)<G.edist y t:=by
  by_cases hcapture:graphSetBall G (graphBallVertices G o ell) 1⊆pairBallVertices G x y r
  · exact Or.inl hcapture
  · right
    intro t ht
    constructor
    · exact lt_of_not_ge (fun hxt=>hcapture (inner_cut_neighborhood_subset_pair_of_near_point G o x y ell r m hm t ht hxt))
    · apply lt_of_not_ge
      intro hyt
      have hh:=inner_cut_neighborhood_subset_pair_of_near_point G o y x ell r m hm t ht hyt
      exact hcapture (fun v hv=>(hh hv).elim Or.inr Or.inl)

theorem cut_neighborhood_captures_inner (G:SimpleGraph V)(T S:Set V)
    (hcapture:graphSetBall G T 1⊆S) : T⊆S:=by
  intro t ht
  exact hcapture ⟨t,ht,by simp⟩

theorem cut_neighborhood_captures_boundary (G:SimpleGraph V)(T S:Set V)
    (hcapture:graphSetBall G T 1⊆S)(e:BoundaryOrientedEdge G T) :
    (boundaryOuterEndpoint G T e).val∈S:=by
  apply hcapture
  exact ⟨e.val.1,e.property.2.1,(SimpleGraph.edist_eq_one_iff_adj.mpr e.property.1).le⟩

namespace LabelledResamplingState
variable {T:Set V}{ι:Type}[Fintype ι]

theorem full_pair_cut_neighborhood_or_roots_far (s:LabelledResamplingState V T ι)
    (selector ell r m:ℕ)(o x y:V)(hT:T=graphBallVertices s.graph o ell)(hm:m+2*ell+1≤r):
    graphSetBall (s.fullResample selector).graph T 1⊆pairBallVertices (s.fullResample selector).graph x y r ∨
      ∀t∈T,(m:ℕ∞)<(s.fullResample selector).graph.edist x t ∧
        (m:ℕ∞)<(s.fullResample selector).graph.edist y t:=by
  have hball:graphBallVertices (s.fullResample selector).graph o ell=T:=by
    simpa only[graphSetBall_singleton] using s.fullResample_ball selector {o} ell
      (by simpa only[graphSetBall_singleton] using hT)
  simpa only[hball] using pair_cut_neighborhood_or_roots_far (s.fullResample selector).graph o x y ell r m hm

theorem full_pair_cut_neighborhood_dichotomy (s:LabelledResamplingState V T ι)
    (selector ell r:ℕ)(o x y:V)(hT:T=graphBallVertices s.graph o ell)(hr:2*ell+1≤r):
    graphSetBall (s.fullResample selector).graph T 1⊆pairBallVertices (s.fullResample selector).graph x y r ∨
      (x∉T ∧ y∉T ∧ ∀t∈T,((r-2*ell-1:ℕ):ℕ∞)<(s.fullResample selector).graph.edist x t ∧
        ((r-2*ell-1:ℕ):ℕ∞)<(s.fullResample selector).graph.edist y t):=by
  rcases s.full_pair_cut_neighborhood_or_roots_far selector ell r (r-2*ell-1) o x y hT (by omega)
    with hcapture|hfar
  · exact Or.inl hcapture
  · refine Or.inr ⟨?_,?_,hfar⟩
    · intro hx
      have hh:((r-2*ell-1:ℕ):ℕ∞)<0:=by simpa only[SimpleGraph.edist_self] using (hfar x hx).1
      exact not_lt_of_ge bot_le hh
    · intro hy
      have hh:((r-2*ell-1:ℕ):ℕ∞)<0:=by simpa only[SimpleGraph.edist_self] using (hfar y hy).2
      exact not_lt_of_ge bot_le hh

end LabelledResamplingState

namespace RegularGraph

theorem eventually_source_full_pair_cut_dichotomy (a d:ℕ)(β:ℝ)
    (ha:0<a)(hd:3≤d)(hβ:0<β):
    ∀ᶠ N:ℕ in Filter.atTop,∀(g:RegularGraph N d)(o:Fin N)(z:ℂ)
      {ι:Type}[Fintype ι]
      (labels:ι≃BoundaryOrientedEdge g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (samples:LocalSamplingFiber g.graph (graphBallVertices g.graph o (actualCavityDepth a d N z-1)))
      (selector:ℕ)(x y:Fin N),
      let ell:=actualCavityDepth a d N z-1
      let T:=graphBallVertices g.graph o ell
      let r:=effectiveModelRadius a d N β
      let s:=g.admissibleState T labels samples
      2*ell+1≤r ∧
      (graphSetBall (s.fullResample selector).graph T 1⊆pairBallVertices (s.fullResample selector).graph x y r ∨
        (x∉T ∧ y∉T ∧ ∀t∈T,((r-2*ell-1:ℕ):ℕ∞)<(s.fullResample selector).graph.edist x t ∧
          ((r-2*ell-1:ℕ):ℕ∞)<(s.fullResample selector).graph.edist y t)):=by
  have hdepth:=(lowerLogLogRadius_tendsto a d ha hd).eventually (Filter.eventually_ge_atTop 4)
  filter_upwards [eventually_resampling_radius_margin a d 4 5 β hd hβ,hdepth] with N hroom hdepthN
  intro g o z ι _ labels samples selector x y
  dsimp only
  let ell:=actualCavityDepth a d N z-1
  let T:=graphBallVertices g.graph o ell
  let r:=effectiveModelRadius a d N β
  let s:=g.admissibleState T labels samples
  have hell:ell≤doubleLogRadius a d N:=(actualCavityDepth_radius_bounds a d N z hdepthN).2
  have hr:2*ell+1≤r:=by dsimp only[r,effectiveModelRadius,modelRadiusLoss];omega
  exact ⟨hr,s.full_pair_cut_neighborhood_dichotomy selector ell r o x y rfl hr⟩

end RegularGraph
end LocalLaw
