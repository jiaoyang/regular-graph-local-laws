import LocalLaw.FullPairCutNeighborhood
import LocalLaw.ShiftedRemainingRadius

/-! # A quarter-radius near/far split for full T harmonic lifting

The close case leaves every inner cut endpoint deep inside the full pair.
The far case forces both original targets outside T. The same statements
hold for arbitrary actual labelled resamplings, and the selected source
radii realize the required margins uniformly in the spectral parameter.
-/
noncomputable section
namespace LocalLaw
local instance quarterCutDichotomyDecidable (p:Prop):Decidable p:=Classical.propDecidable p
variable {V:Type}

def quarterCutClose (G:SimpleGraph V)(T:Set V)(r:ℕ)(x y:V):Prop:=
  ∃t∈T,G.edist x t≤((r/4:ℕ):ℕ∞) ∨ G.edist y t≤((r/4:ℕ):ℕ∞)

def quarterCutLoss (ell r:ℕ):ℕ:=r/4+2*ell+1

theorem inner_cut_neighborhood_close_distance (G:SimpleGraph V)(o x:V)(ell m:ℕ)
    (t:V)(ht:t∈graphBallVertices G o ell)(hxt:G.edist x t≤(m:ℕ∞)):
    ∀v∈graphSetBall G (graphBallVertices G o ell) 1,G.edist x v≤((m+2*ell+1:ℕ):ℕ∞):=by
  intro v hv
  exact (inner_cut_neighborhood_subset_pair_of_near_point G o x x ell (m+2*ell+1) m
    (by omega) t ht hxt hv).elim id id

theorem quarter_close_captures_cut (G:SimpleGraph V)(o x y:V)(ell r:ℕ)
    (hroom:quarterCutLoss ell r≤r)
    (hclose:quarterCutClose G (graphBallVertices G o ell) r x y):
    graphSetBall G (graphBallVertices G o ell) 1⊆pairBallVertices G x y r ∧
      ((∀v∈graphSetBall G (graphBallVertices G o ell) 1,
          G.edist x v≤(quarterCutLoss ell r:ℕ∞)) ∨
        ∀v∈graphSetBall G (graphBallVertices G o ell) 1,
          G.edist y v≤(quarterCutLoss ell r:ℕ∞)):=by
  obtain ⟨t,ht,hx|hy⟩:=hclose
  · exact ⟨inner_cut_neighborhood_subset_pair_of_near_point G o x y ell r (r/4) hroom t ht hx,
      Or.inl (inner_cut_neighborhood_close_distance G o x ell (r/4) t ht hx)⟩
  · refine ⟨?_,Or.inr (inner_cut_neighborhood_close_distance G o y ell (r/4) t ht hy)⟩
    intro v hv
    exact (inner_cut_neighborhood_subset_pair_of_near_point G o y x ell r (r/4) hroom t ht hy hv).elim Or.inr Or.inl

theorem quarter_not_close_roots_far (G:SimpleGraph V)(T:Set V)(r:ℕ)(x y:V)
    (hfar:¬quarterCutClose G T r x y):
    x∉T ∧ y∉T ∧ ∀t∈T,((r/4:ℕ):ℕ∞)<G.edist x t ∧ ((r/4:ℕ):ℕ∞)<G.edist y t:=by
  have hf:∀t∈T,((r/4:ℕ):ℕ∞)<G.edist x t ∧ ((r/4:ℕ):ℕ∞)<G.edist y t:=by
    intro t ht
    exact ⟨lt_of_not_ge (fun hx=>hfar ⟨t,ht,Or.inl hx⟩),
      lt_of_not_ge (fun hy=>hfar ⟨t,ht,Or.inr hy⟩)⟩
  refine ⟨?_,?_,hf⟩
  · intro hx
    have hh:((r/4:ℕ):ℕ∞)<0:=by simpa only[SimpleGraph.edist_self] using (hf x hx).1
    exact not_lt_of_ge bot_le hh
  · intro hy
    have hh:((r/4:ℕ):ℕ∞)<0:=by simpa only[SimpleGraph.edist_self] using (hf y hy).2
    exact not_lt_of_ge bot_le hh

namespace LabelledResamplingState
variable {T:Set V}{ι:Type}[Fintype ι]

theorem full_pair_quarter_cut_dichotomy (s:LabelledResamplingState V T ι)
    (selector ell r:ℕ)(o x y:V)(hT:T=graphBallVertices s.graph o ell)
    (hroom:quarterCutLoss ell r≤r):
    (quarterCutClose (s.fullResample selector).graph T r x y ∧
      graphSetBall (s.fullResample selector).graph T 1⊆pairBallVertices (s.fullResample selector).graph x y r ∧
      ∀v∈graphSetBall (s.fullResample selector).graph T 1∪{x,y},
        (s.fullResample selector).graph.edist x v≤(quarterCutLoss ell r:ℕ∞) ∨
          (s.fullResample selector).graph.edist y v≤(quarterCutLoss ell r:ℕ∞)) ∨
    (x∉T ∧ y∉T ∧ ∀t∈T,((r/4:ℕ):ℕ∞)<(s.fullResample selector).graph.edist x t ∧
      ((r/4:ℕ):ℕ∞)<(s.fullResample selector).graph.edist y t):=by
  let G:=(s.fullResample selector).graph
  by_cases hclose:quarterCutClose G T r x y
  · have hball:graphBallVertices G o ell=T:=by
      simpa only[graphSetBall_singleton] using s.fullResample_ball selector {o} ell
        (by simpa only[graphSetBall_singleton] using hT)
    have hh:=quarter_close_captures_cut G o x y ell r hroom (hball.symm ▸ hclose)
    rw[hball] at hh
    refine Or.inl ⟨hclose,hh.1,?_⟩
    intro v hv
    rcases hv with hv|hv|hv
    · exact hh.2.elim (fun h=>Or.inl (h v hv)) (fun h=>Or.inr (h v hv))
    · subst v
      exact Or.inl (by simp)
    · subst v
      exact Or.inr (by simp)
  · exact Or.inr (quarter_not_close_roots_far G T r x y hclose)

end LabelledResamplingState
namespace RegularGraph

theorem eventually_source_quarter_cut_dichotomy (a d:ℕ)(β:ℝ)
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
      8*ell+8≤r ∧ quarterCutLoss ell r≤r/2 ∧
      ((quarterCutClose (s.fullResample selector).graph T r x y ∧
        graphSetBall (s.fullResample selector).graph T 1⊆pairBallVertices (s.fullResample selector).graph x y r ∧
        ∀v∈graphSetBall (s.fullResample selector).graph T 1∪{x,y},
          (s.fullResample selector).graph.edist x v≤(quarterCutLoss ell r:ℕ∞) ∨
            (s.fullResample selector).graph.edist y v≤(quarterCutLoss ell r:ℕ∞)) ∨
        (x∉T ∧ y∉T ∧ ∀t∈T,((r/4:ℕ):ℕ∞)<(s.fullResample selector).graph.edist x t ∧
          ((r/4:ℕ):ℕ∞)<(s.fullResample selector).graph.edist y t)):=by
  have hdepth:=(lowerLogLogRadius_tendsto a d ha hd).eventually (Filter.eventually_ge_atTop 4)
  filter_upwards [eventually_resampling_radius_margin a d 10 12 β hd hβ,hdepth] with N hroom hdepthN
  intro g o z ι _ labels samples selector x y
  dsimp only
  let ell:=actualCavityDepth a d N z-1
  let T:=graphBallVertices g.graph o ell
  let r:=effectiveModelRadius a d N β
  let s:=g.admissibleState T labels samples
  have hell:ell≤doubleLogRadius a d N:=(actualCavityDepth_radius_bounds a d N z hdepthN).2
  have hr:8*ell+8≤r:=by dsimp only[r,effectiveModelRadius,modelRadiusLoss];omega
  have hloss:quarterCutLoss ell r≤r/2:=by unfold quarterCutLoss;omega
  exact ⟨hr,hloss,s.full_pair_quarter_cut_dichotomy selector ell r o x y rfl (hloss.trans (Nat.div_le_self _ _))⟩

end RegularGraph
end LocalLaw
