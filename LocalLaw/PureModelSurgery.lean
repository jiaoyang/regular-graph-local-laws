import LocalLaw.PhysicalModelLocalization
import LocalLaw.RestrictedSurgeryStability

/-!
# Pure model matching through actual isolated surgery

The old augmented and endpoint restrictions match at the physical boundary
by localization alone. The new endpoint model's proved finite class then
propagates that exponential accuracy to the new augmented endpoint block.
No physical graph local-law error or new augmented finite class is assumed.
-/
open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance pureModelSurgeryDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace DeficientGraph
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I] {d : ℕ}

theorem two_restriction_physical_surgery (g h : DeficientGraph V d) (hd : 3≤d)
    (S T : Set V) (f : I↪V) (hfS : ∀ i,f i∈S) (hfT : ∀ i,f i∈T)
    (hsatG : ∀ v,g.graph.degree v+g.deficit v=d) (hsatH : ∀ v,h.graph.degree v+h.deficit v=d)
    (hgraph : ∀ x y,x∉Set.range f ∨ y∉Set.range f→(g.graph.Adj x y↔h.graph.Adj x y))
    (hOldS : (g.restrict S).ComponentFiniteReferenceBudget)
    (hOldT : (g.restrict T).ComponentFiniteReferenceBudget)
    (hNewT : (h.restrict T).ComponentFiniteReferenceBudget)
    (RS RT RU r m : ℕ) (hRS : ∀ i j,(g.restrict S).graph.dist i j≤RS)
    (hRT : ∀ i j,(g.restrict T).graph.dist i j≤RT)
    (hRU : ∀ i j,(h.restrict T).graph.dist i j≤RU)
    (hcaptureS : ∀ i,graphBallVertices g.graph (f i) r⊆S)
    (hcaptureT : ∀ i,graphBallVertices g.graph (f i) r⊆T)
    (hcount : ∀ c : (h.restrict T).graph.ConnectedComponent,
      Nat.card {i : I // (⟨f i, hfT i⟩ : T) ∈ c.supp} ≤ m)
    (z : ℂ) (hz : 0<z.im)
    (hsmall : (Fintype.card I:ℝ)*(1+endpointSurgeryModelRowCap d m*endpointSurgeryCouplingCap d)*
      endpointSurgeryCouplingCap d*(2*physicalModelTailConstant d*physicalTransfer d z^(2*r))≤1/2) :
    ∀ i j, ‖(h.restrict S).extensionGreen (semicircleRoot z) z ⟨f i,hfS i⟩ ⟨f j,hfS j⟩-
      (h.restrict T).extensionGreen (semicircleRoot z) z ⟨f i,hfT i⟩ ⟨f j,hfT j⟩‖≤
      4*(1+endpointSurgeryModelRowCap d m*endpointSurgeryCouplingCap d)^2*
        physicalModelTailConstant d*physicalTransfer d z^(2*r) := by
  let eS : I↪S:=⟨fun i=>⟨f i,hfS i⟩,fun _ _ hij=>f.injective (congrArg Subtype.val hij)⟩
  let eT : I↪T:=⟨fun i=>⟨f i,hfT i⟩,fun _ _ hij=>f.injective (congrArg Subtype.val hij)⟩
  let R:=((g.restrict S).extensionGreen (semicircleRoot z) z).submatrix eS eS
  let U:=((h.restrict S).extensionGreen (semicircleRoot z) z).submatrix eS eS
  let P:=((g.restrict T).extensionGreen (semicircleRoot z) z).submatrix eT eT
  let Q:=((h.restrict T).extensionGreen (semicircleRoot z) z).submatrix eT eT
  let W:=(h.H-g.H).submatrix f f
  let C:=endpointSurgeryModelRowCap d m
  let w:=endpointSurgeryCouplingCap d
  let δ:=2*physicalModelTailConstant d*physicalTransfer d z^(2*r)
  have hCextra:=finiteExtraReferenceConstant_ge_one d hd
  have hC : 0≤C := by dsimp only [C,endpointSurgeryModelRowCap]; positivity
  have hw : 0≤w := by dsimp only [w,endpointSurgeryCouplingCap]; positivity
  have htail : 0≤physicalModelTailConstant d := by
    have hdR : (3:ℝ)≤d := Nat.cast_le.mpr hd
    have hden : 0<(d:ℝ)-1 := by linarith
    unfold physicalModelTailConstant localizationExceptionalMass
    positivity
  have ht : 0≤physicalTransfer d z := (physicalTransfer_pos d hd z).le
  have hδ : 0≤δ := by dsimp only [δ]; positivity
  have hu:=g.restrict_endpoint_inverse_updates h hd S eS hsatG hsatH hgraph (semicircleRoot z) z hz
    (semicircleRoot_im_pos hz).le
  have hq:=g.restrict_endpoint_inverse_updates h hd T eT hsatG hsatH hgraph (semicircleRoot z) z hz
    (semicircleRoot_im_pos hz).le
  have hU : U+R*W*U=R := hu.1
  have hQ : Q+Q*W*P=P := hq.2
  have hE : ∀ i j, ‖(R-P) i j‖≤δ := by
    intro i j
    exact g.two_restriction_physical_matching hd S T hOldS hOldT RS RT r hRS hRT
      (f i) (f j) (hfS i) (hfS j) (hfT i) (hfT j) (hcaptureS i) (hcaptureS j)
      (hcaptureT i) (hcaptureT j) z hz
  have hrows:=(h.restrict T).componentwise_endpoint_green_rows hd hNewT eT m hcount (semicircleRoot z) z hz
    (semicircleRoot_im_pos hz).le RU hRU (by simp)
  have hQrow : ∀ i,∑ j,‖Q i j‖≤C:=fun i=>hrows.1 (eT i)
  have hQcol : ∀ j,∑ i,‖Q i j‖≤C:=fun j=>hrows.2 (eT j)
  have hWrow : ∀ i,∑ j,‖W i j‖≤w :=
    normalizedAdjacency_difference_endpoint_row_bound g.graph h.graph d g.degree_le h.degree_le f
  have hWcol : ∀ j,∑ i,‖W i j‖≤w :=
    normalizedAdjacency_difference_endpoint_column_bound g.graph h.graph d g.degree_le h.degree_le f
  intro i j
  have hh:=surgery_entry_stability R U P Q W hU hQ C w δ hC hw hδ hQrow hQcol hWrow hWcol hE hsmall i j
  exact hh.trans_eq (by dsimp only [δ]; ring)

end DeficientGraph
end LocalLaw
