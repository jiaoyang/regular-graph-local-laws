import LocalLaw.SourceOmittedLeafInputs
import LocalLaw.AttachedLeafSubfamilyGeneralDecay

/-! # Actual normalized switched-minor decay from the old completion

The kept model has no assumed finite reference class. Its bound follows
from the old-class completion, scalar leaf deletion and q normalization.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 4500000
namespace LocalLaw
local instance actualOmittedKeptLeafDecayDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ}{ι : Type}[Fintype ι]

theorem actual_omitted_kept_leaf_decay (g : RegularGraph N d)(hd : 3≤d)(T : Set (Fin N))
    (labels : ι ≃ BoundaryOrientedEdge g.graph T)(samples : LocalSamplingFiber g.graph T)
    (selector r : ℕ)(S : Set (Tᶜ : Set (Fin N)))(q z : ℂ)(B C1 A L ε : ℝ)
    (hz : 0<z.im)(hq : 0≤q.im)(hp : rationalTreeReference (d-1) q≠0)(hL : 0≤L)(hε : 0≤ε)
    (hinputs : g.OmittedLeafInputs hd T labels samples selector r S q z B C1 A L ε) :
    let s := g.admissibleState T labels samples
    letI : DecidableEq (s.OmittedCore selector S) := fun a b => Classical.propDecidable (a=b)
    let J := s.OmittedOrdinaryLeaves selector S ⊕ s.OmittedExtraLeaves selector S
    letI : DecidableEq J := fun a b => Classical.propDecidable (a=b)
    let R := hereditaryReferenceRadius d (hereditaryReferenceRadius d (augmentedObservationDiameter d r))+2
    let p := rationalTreeReference (d-1) q
    let D := |(treePatchWeakConstant d B A+2*finiteExtraReferenceConstant d)*C1^2|+1
    ∀x:s.OmittedCore selector S,∀l:J,∀h:ℕ,
      (h:ℕ∞)≤(g.omittedCommonModel T labels samples selector S).graph.edist x
        (s.omittedAllMate selector S (s.omittedKeptEmbedding selector S l)) →
      ‖(g.omittedKeptCompletion (by omega) T labels samples selector S).extensionGreen q z (.inl x) (.inr l)‖≤
        (2*finiteExtraReferenceConstant d+‖p⁻¹‖*(2*finiteExtraReferenceConstant d)^2*
          coreConvolutionConstant (finiteOmega d+1)*((R:ℝ)+1))*physicalTransfer d z^h+
        2*‖p⁻¹‖^2*(D*L*ε)*(4*finiteExtraReferenceConstant d)^2+
          omittedNormalizationConstant d B C1*ε := by
  dsimp only
  let s := g.admissibleState T labels samples
  let I := s.OmittedOldLeaves selector S ⊕ s.OmittedExtraLeaves selector S
  let J := s.OmittedOrdinaryLeaves selector S ⊕ s.OmittedExtraLeaves selector S
  letI : DecidableEq (s.OmittedCore selector S) := fun a b => Classical.propDecidable (a=b)
  letI : DecidableEq I := fun a b => Classical.propDecidable (a=b)
  letI : DecidableEq J := fun a b => Classical.propDecidable (a=b)
  let C := g.omittedCommonModel T labels samples selector S
  let H := g.omittedAllCompletion (by omega:1≤d) T labels samples selector S
  let K := g.omittedKeptCompletion (by omega:1≤d) T labels samples selector S
  let e := s.omittedKeptEmbedding selector S
  let p := rationalTreeReference (d-1) q
  let D := |(treePatchWeakConstant d B A+2*finiteExtraReferenceConstant d)*C1^2|+1
  let W := 4*finiteExtraReferenceConstant d
  let R := hereditaryReferenceRadius d (hereditaryReferenceRadius d (augmentedObservationDiameter d r))+2
  have hC : 0≤finiteExtraReferenceConstant d := by linarith [finiteExtraReferenceConstant_ge_one d hd]
  have hW : 0≤W := by dsimp only [W];positivity
  have hσ : 0≤D*L*ε := by dsimp only [D];positivity
  have herr : ∀l k:LeafFamilyComplement e,
      ‖H.extensionGreen q z (.inr l.val) (.inr k.val)-(if l=k then p else 0)‖≤D*L*ε := by
    intro l k
    obtain ⟨i,hi⟩ := s.omittedComplement_is_old selector S l
    obtain ⟨j,hj⟩ := s.omittedComplement_is_old selector S k
    have heq : l=k ↔ i=j := by
      constructor
      · intro h
        exact Sum.inl.inj (hi.symm.trans ((congrArg Subtype.val h).trans hj))
      · intro h
        exact Subtype.ext (hi.trans ((congrArg Sum.inl h).trans hj.symm))
    simpa only [hi,hj,heq] using hinputs.2.2.2.2.1 i j
  have hn : (Fintype.card (LeafFamilyComplement e):ℝ)≤(Fintype.card I:ℝ) := by
    exact_mod_cast Fintype.card_subtype_le (fun l => l∉Set.range e)
  have hsmall : (Fintype.card (LeafFamilyComplement e):ℝ)*‖p⁻¹‖*(D*L*ε)≤1/2 :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hn (norm_nonneg _)) hσ).trans hinputs.2.2.2.2.2.1
  intro x l h hfar
  have hfarH : (h:ℕ∞)≤(multiLeafGraph C.graph (s.omittedAllMate selector S)).edist
      (Sum.map id e (.inl x)) (Sum.map id e (.inr l)) :=
    hfar.trans (multiLeafGraph_edist_projection C.graph (s.omittedAllMate selector S) (.inl x) (.inr (e l)))
  have hdec := C.attachLeaves_subfamily_general_decay hd (s.omittedAllMate selector S)
    (g.omittedAllMate_restore_budget T labels samples selector S) e q z p hz hq hp
    hinputs.1 R hinputs.2.1 hinputs.2.2.2.1 (D*L*ε) W hσ hW herr hsmall hinputs.2.2.2.2.2.2 (.inl x) (.inr l) h hfarH
  have hCpos : 0≤finiteExtraReferenceConstant d := by linarith [finiteExtraReferenceConstant_ge_one d hd]
  have hN : 0≤omittedNormalizationConstant d B C1 := by
    unfold omittedNormalizationConstant omittedNormalizationCoefficient omittedKeptRowConstant
    positivity
  exact hdec.trans (le_add_of_nonneg_right (mul_nonneg hN hε))

end RegularGraph
end LocalLaw
