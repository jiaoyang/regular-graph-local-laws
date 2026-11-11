import LocalLaw.OmittedKeptBoundaryGeometry

/-! # Both original pair centers give the exact shifted kept-slot distance -/

noncomputable section
namespace LocalLaw
namespace LabelledResamplingState
variable {V : Type}[Fintype V]{T : Set V}{ι : Type}[Fintype ι]

omit [Fintype V] in
theorem shifted_omittedKept_root_distance_right (s : LabelledResamplingState V T ι)(selector r h:ℕ)
    (hh:h≤r)(x y:(Tᶜ:Set V))
    (u:s.OmittedCore selector (pairBallVertices (outsideGraph (s.fullResample selector).graph T) x y r))
    (hu:(outsideGraph (s.fullResample selector).graph T).edist y u.val.val≤((r-h:ℕ):ℕ∞))
    (l:s.OmittedOrdinaryLeaves selector (pairBallVertices (outsideGraph (s.fullResample selector).graph T) x y r) ⊕
      s.OmittedExtraLeaves selector (pairBallVertices (outsideGraph (s.fullResample selector).graph T) x y r)) :
    let S := pairBallVertices (outsideGraph (s.fullResample selector).graph T) x y r
    (h:ℕ∞)≤(((outsideGraph s.graph T).induce (s.selectedFirstSet selector)ᶜ).induce
      {v:((s.selectedFirstSet selector)ᶜ:Set (Tᶜ:Set V)) | v.val∈S}).edist
      u (s.omittedAllMate selector S (s.omittedKeptEmbedding selector S l)) := by
  dsimp only
  let S := pairBallVertices (outsideGraph (s.fullResample selector).graph T) x y r
  let v := s.omittedAllMate selector S (s.omittedKeptEmbedding selector S l)
  let G := outsideGraph (s.fullResample selector).graph T
  have hsum : (r:ℕ∞)≤((r-h:ℕ):ℕ∞)+G.edist u.val.val v.val.val :=
    (s.omittedKept_pair_boundary_depth selector r x y l).2.trans
      ((SimpleGraph.edist_triangle (G:=G) (u:=y) (v:=u.val.val) (w:=v.val.val)).trans (add_le_add_right hu _))
  have heq : (r:ℕ∞)=((r-h:ℕ):ℕ∞)+(h:ℕ∞) := by norm_cast;omega
  rw [heq] at hsum
  have hf : (h:ℕ∞)≤G.edist u.val.val v.val.val :=
    (WithTop.add_le_add_iff_left (by simp : ((r-h:ℕ):ℕ∞)≠⊤)).mp hsum
  exact hf.trans (graphHom_edist_le (s.omittedCommonNewHom selector S) u v)

end LabelledResamplingState
end LocalLaw
