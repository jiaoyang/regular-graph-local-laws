import LocalLaw.ComponentFiniteLocalization
import LocalLaw.PairRestrictionIdentity

/-!
# Pure physical-boundary finite-model matching

At q=m_sc the refined ordinary feedback vanishes identically. Actual model
localization therefore pays only the exponential tail, without a source
physical Green error or weak-prior hypothesis.
-/
noncomputable section
namespace LocalLaw
local instance physicalModelLocalizationDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def physicalModelTailConstant (d : ℕ) : ℝ :=
  8*finiteExtraReferenceConstant d^2*DeficientGraph.localizationExceptionalMass d (1:ℂ)+
  4*finiteExtraReferenceConstant d^2*(((finiteOmega d:ℝ)+1)/((d:ℝ)-1))+2*finiteExtraReferenceConstant d

namespace DeficientGraph
variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

theorem physical_pair_localization (g : DeficientGraph V d) (hd : 3≤d)
    (hbudget : g.ComponentFiniteReferenceBudget) (R r : ℕ) (hR : ∀ i j,g.graph.dist i j≤R)
    (z : ℂ) (hz : 0<z.im) (i j : V) :
    ‖g.extensionGreen (semicircleRoot z) z i j-g.P r z (semicircleRoot z) i j‖≤
      physicalModelTailConstant d*physicalTransfer d z^(2*r) := by
  have hτ : ordinaryFeedbackBudget z (semicircleRoot z) ‖z‖ R=0 := by simp [ordinaryFeedbackBudget]
  have hh:=g.componentwise_pair_localization hd hbudget (semicircleRoot z) z hz (semicircleRoot_im_pos hz).le
    ‖z‖ le_rfl R r hR (by simp) (by simp) (by simp) (by simp) (by rw [hτ]; simp) i j
  have hC : 0≤finiteExtraReferenceConstant d := (by norm_num : (0:ℝ)≤1).trans (finiteExtraReferenceConstant_ge_one d hd)
  have hdR : (3:ℝ)≤d := Nat.cast_le.mpr hd
  have hden : 0≤(d:ℝ)-1 := by linarith
  have hmass : localizationExceptionalMass d (semicircleRoot z)≤localizationExceptionalMass d (1:ℂ) := by
    unfold localizationExceptionalMass
    rw [norm_one]
    apply div_le_div_of_nonneg_right _ hden
    exact add_le_add_left (mul_le_mul_of_nonneg_right (semicircleRoot_norm_le_one z) (by positivity)) _
  have hratio : 0≤((finiteOmega d:ℝ)+1)/((d:ℝ)-1) := div_nonneg (by positivity) hden
  apply hh.trans
  unfold finitePairLocalizationBound
  rw [hτ]
  simp only [mul_zero,zero_add]
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (physicalTransfer_pos d hd z).le _)
  unfold physicalModelTailConstant
  have hfirst:=mul_le_mul_of_nonneg_left hmass (by positivity : 0≤8*finiteExtraReferenceConstant d^2)
  have hsecond:=mul_le_mul_of_nonneg_left (semicircleRoot_norm_le_one z)
    (by positivity : 0≤4*finiteExtraReferenceConstant d^2*(((finiteOmega d:ℝ)+1)/((d:ℝ)-1)))
  nlinarith only [hfirst,hsecond]

/-- Two genuine old restrictions capturing the same endpoint balls match
at the physical boundary up to twice the pure localization tail. -/
theorem two_restriction_physical_matching (g : DeficientGraph V d) (hd : 3≤d)
    (S T : Set V) (hS : (g.restrict S).ComponentFiniteReferenceBudget)
    (hT : (g.restrict T).ComponentFiniteReferenceBudget)
    (RS RT r : ℕ) (hRS : ∀ i j,(g.restrict S).graph.dist i j≤RS)
    (hRT : ∀ i j,(g.restrict T).graph.dist i j≤RT)
    (i j : V) (hiS : i∈S) (hjS : j∈S) (hiT : i∈T) (hjT : j∈T)
    (hiBallS : graphBallVertices g.graph i r⊆S) (hjBallS : graphBallVertices g.graph j r⊆S)
    (hiBallT : graphBallVertices g.graph i r⊆T) (hjBallT : graphBallVertices g.graph j r⊆T)
    (z : ℂ) (hz : 0<z.im) :
    ‖(g.restrict S).extensionGreen (semicircleRoot z) z ⟨i,hiS⟩ ⟨j,hjS⟩-
      (g.restrict T).extensionGreen (semicircleRoot z) z ⟨i,hiT⟩ ⟨j,hjT⟩‖≤
        2*physicalModelTailConstant d*physicalTransfer d z^(2*r) := by
  have hs:=(g.restrict S).physical_pair_localization hd hS RS r hRS z hz ⟨i,hiS⟩ ⟨j,hjS⟩
  have ht:=(g.restrict T).physical_pair_localization hd hT RT r hRT z hz ⟨i,hiT⟩ ⟨j,hjT⟩
  rw [g.restrict_pair_P S ⟨i,hiS⟩ ⟨j,hjS⟩ r hiBallS hjBallS] at hs
  rw [g.restrict_pair_P T ⟨i,hiT⟩ ⟨j,hjT⟩ r hiBallT hjBallT] at ht
  exact ((norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
    (add_le_add hs (by simpa only [norm_sub_rev] using ht))).trans_eq (by ring)

end DeficientGraph
end LocalLaw
