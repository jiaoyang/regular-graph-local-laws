import LocalLaw.OmittedKeptBoundaryGeometry
import LocalLaw.FullOutsideReplacement
import LocalLaw.RemainingPairMixedRadius
import LocalLaw.DeletedCouplingFarBound

/-! # Kept-slot distances for the exterior slice of a full pair

The omitted sampled B vertex is outside the literal FULL pair, even if a
short full path passes through T. The crossing-edge boundary depth is thus
measured in the correct ambient switched metric. Both original centers,
inside or outside T, give the exact shifted distance to each kept mate.
-/
noncomputable section
namespace LocalLaw
local instance fullPairOmittedGeometryDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace LabelledResamplingState
variable {V:Type}{T:Set V}{ι:Type}[Fintype ι]

theorem omittedKept_full_pair_boundary_depth (s:LabelledResamplingState V T ι)
    (selector r:ℕ)(x y:V)
    (l:s.OmittedOrdinaryLeaves selector (s.fullSliceOutside (pairBallVertices (s.fullResample selector).graph x y r))⊕
      s.OmittedExtraLeaves selector (s.fullSliceOutside (pairBallVertices (s.fullResample selector).graph x y r))):
    let S:=s.fullSliceOutside (pairBallVertices (s.fullResample selector).graph x y r)
    let v:=s.omittedAllMate selector S (s.omittedKeptEmbedding selector S l)
    (r:ℕ∞)≤(s.fullResample selector).graph.edist x v.val.val.val ∧
      (r:ℕ∞)≤(s.fullResample selector).graph.edist y v.val.val.val:=by
  dsimp only
  let S:=s.fullSliceOutside (pairBallVertices (s.fullResample selector).graph x y r)
  let v:=s.omittedAllMate selector S (s.omittedKeptEmbedding selector S l)
  let e:=s.omittedKeptNewIncident selector S l
  let b:=s.admissibleSampleVertex selector e.val
  have hb:b.val∉pairBallVertices (s.fullResample selector).graph x y r:=e.property.1
  have hv:v.val.val.val∈pairBallVertices (s.fullResample selector).graph x y r:=v.property
  let edge:BoundaryOrientedEdge (s.fullResample selector).graph
      (pairBallVertices (s.fullResample selector).graph x y r):=
    ⟨(v.val.val.val,b.val),e.property.2.symm,hv,hb⟩
  exact pair_boundary_inner_edist_lower _ x y r edge

theorem shifted_omittedKept_full_root_distance (s:LabelledResamplingState V T ι)
    (selector r h:ℕ)(hh:h≤r)(x y:V)
    (u:s.OmittedCore selector (s.fullSliceOutside (pairBallVertices (s.fullResample selector).graph x y r)))
    (hu:h=0 ∨ (s.fullResample selector).graph.edist x u.val.val.val≤((r-h:ℕ):ℕ∞) ∨
      (s.fullResample selector).graph.edist y u.val.val.val≤((r-h:ℕ):ℕ∞))
    (l:s.OmittedOrdinaryLeaves selector (s.fullSliceOutside (pairBallVertices (s.fullResample selector).graph x y r))⊕
      s.OmittedExtraLeaves selector (s.fullSliceOutside (pairBallVertices (s.fullResample selector).graph x y r))):
    let S:=s.fullSliceOutside (pairBallVertices (s.fullResample selector).graph x y r)
    (h:ℕ∞)≤(((outsideGraph s.graph T).induce (s.selectedFirstSet selector)ᶜ).induce
      {v:((s.selectedFirstSet selector)ᶜ:Set (Tᶜ:Set V))|v.val∈S}).edist
        u (s.omittedAllMate selector S (s.omittedKeptEmbedding selector S l)):=by
  dsimp only
  let S:=s.fullSliceOutside (pairBallVertices (s.fullResample selector).graph x y r)
  let v:=s.omittedAllMate selector S (s.omittedKeptEmbedding selector S l)
  let G:=(s.fullResample selector).graph
  have hmetric:G.edist u.val.val.val v.val.val.val≤
      (((outsideGraph s.graph T).induce (s.selectedFirstSet selector)ᶜ).induce
        {v:((s.selectedFirstSet selector)ᶜ:Set (Tᶜ:Set V))|v.val∈S}).edist u v:=
    (ambient_edist_le_induced_edist G Tᶜ u.val.val v.val.val).trans
      (graphHom_edist_le (s.omittedCommonNewHom selector S) u v)
  have hshift (a:V)(ha:(r:ℕ∞)≤G.edist a v.val.val.val)
      (hau:G.edist a u.val.val.val≤((r-h:ℕ):ℕ∞)):
      (h:ℕ∞)≤G.edist u.val.val.val v.val.val.val:=by
    have hsum:(r:ℕ∞)≤((r-h:ℕ):ℕ∞)+G.edist u.val.val.val v.val.val.val:=
      ha.trans ((SimpleGraph.edist_triangle (G:=G) (u:=a) (v:=u.val.val.val) (w:=v.val.val.val)).trans (add_le_add_right hau _))
    have heq:(r:ℕ∞)=((r-h:ℕ):ℕ∞)+(h:ℕ∞):=by norm_cast;omega
    rw[heq] at hsum
    exact (WithTop.add_le_add_iff_left (by simp:((r-h:ℕ):ℕ∞)≠⊤)).mp hsum
  rcases hu with hzero|hx|hy
  · subst h
    exact bot_le
  · exact (hshift x (s.omittedKept_full_pair_boundary_depth selector r x y l).1 hx).trans hmetric
  · exact (hshift y (s.omittedKept_full_pair_boundary_depth selector r x y l).2 hy).trans hmetric


theorem omittedKept_full_boundary_depth_of_contains_pair (s:LabelledResamplingState V T ι)
    (selector r:ℕ)(S:Set (Tᶜ:Set V))(x y:V)
    (hcontain:s.fullSliceOutside (pairBallVertices (s.fullResample selector).graph x y r)⊆S)
    (l:s.OmittedOrdinaryLeaves selector S⊕s.OmittedExtraLeaves selector S):
    let v:=s.omittedAllMate selector S (s.omittedKeptEmbedding selector S l)
    (r:ℕ∞)≤(s.fullResample selector).graph.edist x v.val.val.val ∧
      (r:ℕ∞)≤(s.fullResample selector).graph.edist y v.val.val.val:=by
  dsimp only
  let v:=s.omittedAllMate selector S (s.omittedKeptEmbedding selector S l)
  let e:=s.omittedKeptNewIncident selector S l
  let b:=s.admissibleSampleVertex selector e.val
  have hb:b.val∉pairBallVertices (s.fullResample selector).graph x y r:=
    fun hb=>e.property.1 (hcontain hb)
  exact omitted_pair_neighbor_far (s.fullResample selector).graph x y b.val v.val.val.val r hb e.property.2.symm

theorem shifted_omittedKept_full_distance_of_contains_pair (s:LabelledResamplingState V T ι)
    (selector r h:ℕ)(hh:h≤r)(S:Set (Tᶜ:Set V))(x y:V)
    (hcontain:s.fullSliceOutside (pairBallVertices (s.fullResample selector).graph x y r)⊆S)
    (u:s.OmittedCore selector S)
    (hu:h=0 ∨ (s.fullResample selector).graph.edist x u.val.val.val≤((r-h:ℕ):ℕ∞) ∨
      (s.fullResample selector).graph.edist y u.val.val.val≤((r-h:ℕ):ℕ∞))
    (l:s.OmittedOrdinaryLeaves selector S⊕s.OmittedExtraLeaves selector S):
    (h:ℕ∞)≤(((outsideGraph s.graph T).induce (s.selectedFirstSet selector)ᶜ).induce
      {v:((s.selectedFirstSet selector)ᶜ:Set (Tᶜ:Set V))|v.val∈S}).edist
        u (s.omittedAllMate selector S (s.omittedKeptEmbedding selector S l)):=by
  let v:=s.omittedAllMate selector S (s.omittedKeptEmbedding selector S l)
  let G:=(s.fullResample selector).graph
  have hmetric:G.edist u.val.val.val v.val.val.val≤
      (((outsideGraph s.graph T).induce (s.selectedFirstSet selector)ᶜ).induce
        {v:((s.selectedFirstSet selector)ᶜ:Set (Tᶜ:Set V))|v.val∈S}).edist u v:=
    (ambient_edist_le_induced_edist G Tᶜ u.val.val v.val.val).trans
      (graphHom_edist_le (s.omittedCommonNewHom selector S) u v)
  have hshift (a:V)(ha:(r:ℕ∞)≤G.edist a v.val.val.val)
      (hau:G.edist a u.val.val.val≤((r-h:ℕ):ℕ∞)):
      (h:ℕ∞)≤G.edist u.val.val.val v.val.val.val:=by
    have hsum:(r:ℕ∞)≤((r-h:ℕ):ℕ∞)+G.edist u.val.val.val v.val.val.val:=
      ha.trans ((SimpleGraph.edist_triangle (G:=G) (u:=a) (v:=u.val.val.val) (w:=v.val.val.val)).trans (add_le_add_right hau _))
    have heq:(r:ℕ∞)=((r-h:ℕ):ℕ∞)+(h:ℕ∞):=by norm_cast;omega
    rw[heq] at hsum
    exact (WithTop.add_le_add_iff_left (by simp:((r-h:ℕ):ℕ∞)≠⊤)).mp hsum
  rcases hu with hzero|hx|hy
  · subst h
    exact bot_le
  · exact (hshift x (s.omittedKept_full_boundary_depth_of_contains_pair selector r S x y hcontain l).1 hx).trans hmetric
  · exact (hshift y (s.omittedKept_full_boundary_depth_of_contains_pair selector r S x y hcontain l).2 hy).trans hmetric

end LabelledResamplingState
end LocalLaw
