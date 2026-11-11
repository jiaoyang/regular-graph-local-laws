import LocalLaw.RestrictedPerturbationIdentity

/-!
# The actual model correction when surgery crosses a restriction boundary

The physical adjacency update alone is insufficient for a switched pair
ball. A literal diagonal correction counts changed neighbors outside the
restriction. It vanishes only where the crossing adjacencies agree.
-/
open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance partialSurgeryIdentityDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace DeficientGraph
variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

def crossingChargeDifference (g h : DeficientGraph V d) (S : Set V) (v : S) : ℝ :=
  ((Nat.card {w : (Sᶜ : Set V) // h.graph.Adj w.val v.val}:ℝ)-
    (Nat.card {w : (Sᶜ : Set V) // g.graph.Adj w.val v.val}:ℝ))/((d:ℝ)-1)

omit [DecidableEq V] in
theorem restrict_boundaryCoefficient_difference (g h : DeficientGraph V d) (S : Set V)
    (hsatG : ∀ v,g.graph.degree v+g.deficit v=d)
    (hsatH : ∀ v,h.graph.degree v+h.deficit v=d) (v : S) :
    (h.restrict S).boundaryCoefficient v-(g.restrict S).boundaryCoefficient v=
      g.crossingChargeDifference h S v := by
  rw [g.restrict_boundaryCoefficient_eq_outside_neighbors S hsatG,
    h.restrict_boundaryCoefficient_eq_outside_neighbors S hsatH]
  exact (sub_div ..).symm

/-- Crossing-edge surgery changes the extension boundary coefficient as
well as its physical adjacency. This exact correction is not omitted. -/
theorem restrict_extensionMatrix_difference_partial (g h : DeficientGraph V d) (S : Set V)
    (hsatG : ∀ v,g.graph.degree v+g.deficit v=d)
    (hsatH : ∀ v,h.graph.degree v+h.deficit v=d) (q z : ℂ) :
    (h.restrict S).extensionMatrix q z-(g.restrict S).extensionMatrix q z=
      (h.H-g.H).submatrix (Subtype.val:S→V) (Subtype.val:S→V)-
        q • Matrix.diagonal (fun v:S=>(g.crossingChargeDifference h S v:ℂ)) := by
  have hD : (h.restrict S).boundaryDiagonal-(g.restrict S).boundaryDiagonal=
      Matrix.diagonal (fun v:S=>(g.crossingChargeDifference h S v:ℂ)) := by
    unfold boundaryDiagonal
    rw [Matrix.diagonal_sub]
    apply congrArg (fun f : S→ℂ => Matrix.diagonal f)
    funext v
    change ((h.restrict S).boundaryCoefficient v:ℂ)-((g.restrict S).boundaryCoefficient v:ℂ)=_
    rw [←Complex.ofReal_sub,g.restrict_boundaryCoefficient_difference h S hsatG hsatH]
  change (spectralMatrix (h.restrict S).H z-q • (h.restrict S).boundaryDiagonal)-
    (spectralMatrix (g.restrict S).H z-q • (g.restrict S).boundaryDiagonal)=_
  rw [h.H_restrict,g.H_restrict,Matrix.submatrix_sub,←hD,smul_sub]
  unfold spectralMatrix
  ext i j
  simp only [Pi.sub_apply,Matrix.sub_apply,Matrix.submatrix_apply,Matrix.smul_apply,smul_eq_mul]
  ring

omit [DecidableEq V] in
theorem crossingChargeDifference_eq_zero_of_agreement (g h : DeficientGraph V d)
    (S : Set V) (v : S)
    (hcross : ∀ w : (Sᶜ : Set V),g.graph.Adj v.val w.val↔h.graph.Adj v.val w.val) :
    g.crossingChargeDifference h S v=0 := by
  have hc : Nat.card {w : (Sᶜ : Set V) // h.graph.Adj w.val v.val}=
      Nat.card {w : (Sᶜ : Set V) // g.graph.Adj w.val v.val} := by
    apply Nat.card_congr
    exact
      { toFun:=fun w=>⟨w.val,((hcross w.val).mpr w.property.symm).symm⟩
        invFun:=fun w=>⟨w.val,((hcross w.val).mp w.property.symm).symm⟩
        left_inv:=fun _=>rfl
        right_inv:=fun _=>rfl }
  simp only [crossingChargeDifference,hc,sub_self,zero_div]

end DeficientGraph
end LocalLaw
