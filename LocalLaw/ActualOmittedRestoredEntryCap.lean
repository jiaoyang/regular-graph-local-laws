import LocalLaw.ActualOmittedRestoredDecay
import LocalLaw.AttachedLeafSubfamilyEntryCap

/-! # A fixed cap for the true normalized switched deleted core -/

noncomputable section
set_option maxHeartbeats 3500000
namespace LocalLaw
local instance actualOmittedEntryCapDecidable (p:Prop):Decidable p:=Classical.propDecidable p

def omittedRestoredEntryCap (d:ℕ)(B C1:ℝ):ℝ:=
  2*finiteExtraReferenceConstant d+
    2*(4*finiteExtraReferenceConstant d)*(2*|B|+3)*(2*finiteExtraReferenceConstant d)+
      omittedNormalizationConstant d B C1

namespace RegularGraph
variable {N d:ℕ}{ι:Type}[Fintype ι]

theorem actual_omitted_restored_entry_cap (g : RegularGraph N d)(hd : 3≤d)(T : Set (Fin N))
    (labels : ι ≃ BoundaryOrientedEdge g.graph T)(samples : LocalSamplingFiber g.graph T)
    (selector r : ℕ)(S : Set (Tᶜ : Set (Fin N)))(q z : ℂ)(B C1 A L ε : ℝ)
    (hz : 0<z.im)(hq : 0≤q.im)(hp : rationalTreeReference (d-1) q≠0)
    (hpInv : ‖(rationalTreeReference (d-1) q)⁻¹‖≤2*|B|+3)(hL : 0≤L)(hε : 0≤ε)(hε1 : ε≤1)
    (hinputs : g.OmittedLeafInputs hd T labels samples selector r S q z B C1 A L ε)
    (hcontrol : g.OmittedKeptControlled hd T labels samples selector S q z B C1 ε) :
    let s := g.admissibleState T labels samples
    letI : DecidableEq (s.OmittedCore selector S) := fun a b => Classical.propDecidable (a=b)
    ∀x y:s.OmittedCore selector S,
      ‖(g.omittedKeptRestoredModel T labels samples selector S).extensionGreen q z x y‖≤
        omittedRestoredEntryCap d B C1 := by
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
  have hC2 : 0≤2*finiteExtraReferenceConstant d := by positivity
  have hρ : 0≤physicalTransfer d z := (physicalTransfer_pos d hd z).le
  have hρ1 : physicalTransfer d z≤1 := by nlinarith [physicalTransfer_sq_le_half d hd z]
  have hall : ∀a b,‖H.extensionGreen q z a b‖≤2*finiteExtraReferenceConstant d := by
    intro a b
    exact (H.componentwise_finite_kernel_decay hd hinputs.1 q z hz hq R hinputs.2.1
      hinputs.2.2.2.1 a b).trans (mul_le_of_le_one_right hC2 (pow_le_one₀ hρ hρ1))
  have hk := C.attachLeaves_subfamily_entry_cap hd (s.omittedAllMate selector S)
    (g.omittedAllMate_restore_budget T labels samples selector S) e q z p hz hq hp
    (D*L*ε) W (2*finiteExtraReferenceConstant d) hσ hC2 herr hsmall hinputs.2.2.2.2.2.2 hall
  intro x y
  have hdec : ‖K.extensionGreen q z (.inl x) (.inl y)‖≤
      2*finiteExtraReferenceConstant d+2*W*(2*|B|+3)*(2*finiteExtraReferenceConstant d) :=
    (hk (.inl x) (.inl y)).trans (by gcongr)
  have hnorm := hcontrol.2.2 x y
  have htri : ‖(g.omittedKeptRestoredModel T labels samples selector S).extensionGreen q z x y‖≤
      ‖K.extensionGreen q z (.inl x) (.inl y)‖+
      ‖K.extensionGreen q z (.inl x) (.inl y)-
        (g.omittedKeptRestoredModel T labels samples selector S).extensionGreen q z x y‖ := by
    have hh := norm_add_le (K.extensionGreen q z (.inl x) (.inl y))
      ((g.omittedKeptRestoredModel T labels samples selector S).extensionGreen q z x y-K.extensionGreen q z (.inl x) (.inl y))
    rw [add_sub_cancel,norm_sub_rev] at hh
    exact hh
  have hN : 0≤omittedNormalizationConstant d B C1 := by
    unfold omittedNormalizationConstant omittedNormalizationCoefficient omittedKeptRowConstant
    positivity
  have hn := hnorm.trans (mul_le_of_le_one_right hN hε1)
  exact htri.trans ((add_le_add hdec hn).trans_eq (by rfl))

end RegularGraph
end LocalLaw
