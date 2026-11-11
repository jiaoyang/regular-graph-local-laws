import LocalLaw.OmittedLeafData
import LocalLaw.OmittedLeafEmbedding

/-! # Kept-slot roots lie on the actual switched pair boundary

Every ordinary or added kept slot is a literal omitted NEW B-neighbor.
Its root is far from both original targets, and a secondary core target
inherits the exact shifted distance, without a half-radius loss.
-/

noncomputable section
namespace LocalLaw
local instance omittedKeptBoundaryGeometryDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace LabelledResamplingState
variable {V : Type}[Fintype V]{T : Set V}{ι : Type}[Fintype ι]

def omittedKeptNewIncident (s : LabelledResamplingState V T ι)(selector : ℕ)
    (S : Set (Tᶜ:Set V))(l:s.OmittedOrdinaryLeaves selector S⊕s.OmittedExtraLeaves selector S) :
    s.OmittedNewIncident selector S ((s.omittedAllMate selector S (s.omittedKeptEmbedding selector S l)).val.val) :=
  match l with
  | .inl l => (s.omittedNewIncidentEquiv selector S l.1.val.val).symm (.inl l.2)
  | .inr i => (s.omittedNewIncidentEquiv selector S (s.admissibleBoundaryVertex selector i.val)).symm
      (.inr ⟨i.val,i.property.1,rfl⟩)

omit [Fintype V] in
theorem omittedKept_pair_boundary_depth (s : LabelledResamplingState V T ι)(selector r : ℕ)
    (x y:(Tᶜ:Set V))
    (l:s.OmittedOrdinaryLeaves selector (pairBallVertices (outsideGraph (s.fullResample selector).graph T) x y r) ⊕
      s.OmittedExtraLeaves selector (pairBallVertices (outsideGraph (s.fullResample selector).graph T) x y r)) :
    let S := pairBallVertices (outsideGraph (s.fullResample selector).graph T) x y r
    let v := s.omittedAllMate selector S (s.omittedKeptEmbedding selector S l)
    (r:ℕ∞)≤(outsideGraph (s.fullResample selector).graph T).edist x v.val.val ∧
      (r:ℕ∞)≤(outsideGraph (s.fullResample selector).graph T).edist y v.val.val := by
  dsimp only
  exact s.omittedNewIncident_pair_boundary_depth selector r x y _
    (s.omittedAllMate selector _ (s.omittedKeptEmbedding selector _ l)).property
    (s.omittedKeptNewIncident selector _ l)

def omittedCommonNewHom (s : LabelledResamplingState V T ι)(selector : ℕ)(S:Set (Tᶜ:Set V)) :
    (((outsideGraph s.graph T).induce (s.selectedFirstSet selector)ᶜ).induce {v:((s.selectedFirstSet selector)ᶜ:Set (Tᶜ:Set V)) | v.val∈S}) →g
      outsideGraph (s.fullResample selector).graph T where
  toFun v := v.val.val
  map_rel' := fun {u v} h => (s.fullResample_without_selectedFirst_adj selector u.val v.val).mpr h

omit [Fintype V] in
theorem shifted_omittedKept_root_distance (s : LabelledResamplingState V T ι)(selector r h:ℕ)
    (hh:h≤r)(x y:(Tᶜ:Set V))
    (u:s.OmittedCore selector (pairBallVertices (outsideGraph (s.fullResample selector).graph T) x y r))
    (hu:(outsideGraph (s.fullResample selector).graph T).edist x u.val.val≤((r-h:ℕ):ℕ∞))
    (l:s.OmittedOrdinaryLeaves selector (pairBallVertices (outsideGraph (s.fullResample selector).graph T) x y r) ⊕
      s.OmittedExtraLeaves selector (pairBallVertices (outsideGraph (s.fullResample selector).graph T) x y r)) :
    let S := pairBallVertices (outsideGraph (s.fullResample selector).graph T) x y r
    (h:ℕ∞)≤(((outsideGraph s.graph T).induce (s.selectedFirstSet selector)ᶜ).induce {v:((s.selectedFirstSet selector)ᶜ:Set (Tᶜ:Set V)) | v.val∈S}).edist
      u (s.omittedAllMate selector S (s.omittedKeptEmbedding selector S l)) := by
  dsimp only
  let S := pairBallVertices (outsideGraph (s.fullResample selector).graph T) x y r
  let v := s.omittedAllMate selector S (s.omittedKeptEmbedding selector S l)
  let G := outsideGraph (s.fullResample selector).graph T
  have hsum : (r:ℕ∞)≤((r-h:ℕ):ℕ∞)+G.edist u.val.val v.val.val :=
    (s.omittedKept_pair_boundary_depth selector r x y l).1.trans
      ((SimpleGraph.edist_triangle (G:=G) (u:=x) (v:=u.val.val) (w:=v.val.val)).trans (add_le_add_right hu _))
  have heq : (r:ℕ∞)=((r-h:ℕ):ℕ∞)+(h:ℕ∞) := by norm_cast;omega
  rw [heq] at hsum
  have hf : (h:ℕ∞)≤G.edist u.val.val v.val.val :=
    (WithTop.add_le_add_iff_left (by simp : ((r-h:ℕ):ℕ∞)≠⊤)).mp hsum
  exact hf.trans (graphHom_edist_le (s.omittedCommonNewHom selector S) u v)

end LabelledResamplingState
end LocalLaw
