import LocalLaw.SourceLocalCommonRows
import LocalLaw.OmittedKeptMateRows
import LocalLaw.OmittedKeptLeafUniformDecay
import LocalLaw.AttachedLeafTargetBound

/-! # Actual asymmetric common-to-switched deleted completion comparison

Every old lost-neighbor slot, including omitted B incidences, is retained
in the common model. Kept leaf inverse rows follow from its actual mate/A
rows. Remote target bounds are proved by the old-class completion, and the
q-normalization error is the actual new-core error.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 4000000
namespace LocalLaw
local instance actualOmittedCompletionComparisonDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace RegularGraph
variable {N d : ℕ}{ι : Type}[Fintype ι]

theorem localCommonRows_kept_mates (g : RegularGraph N d)(T:Set (Fin N))
    (labels:ι≃BoundaryOrientedEdge g.graph T)(samples:LocalSamplingFiber g.graph T)
    (selector:ℕ)(S:Set (Tᶜ:Set (Fin N)))(q z:ℂ)(KM KA:ℝ)
    (hr:g.LocalCommonIncidenceRows T labels samples selector S q z KM KA) :
    let s:=g.admissibleState T labels samples
    letI:DecidableEq (s.OmittedCore selector S):=fun a b=>Classical.propDecidable (a=b)
    ∀u:s.OmittedCore selector S,
      (∑l:s.OmittedOrdinaryLeaves selector S⊕s.OmittedExtraLeaves selector S,
        ‖(g.omittedCommonModel T labels samples selector S).extensionGreen q z u
          (s.omittedAllMate selector S (s.omittedKeptEmbedding selector S l))‖)≤KM+KA := by
  dsimp only
  let s:=g.admissibleState T labels samples
  letI:DecidableEq (s.OmittedCore selector S):=fun a b=>Classical.propDecidable (a=b)
  exact s.omittedKept_mate_rows_of_old_boundary selector S
    ((g.omittedCommonModel T labels samples selector S).extensionGreen q z) KM KA hr.1.1 hr.2.1

theorem actual_omitted_completion_comparison (g:RegularGraph N d)(hd:3≤d)(T:Set (Fin N))
    (labels:ι≃BoundaryOrientedEdge g.graph T)(samples:LocalSamplingFiber g.graph T)
    (selector:ℕ)(S:Set (Tᶜ:Set (Fin N)))(q z:ℂ)(B C1 A L ε KM KA:ℝ)
    (hz:0<z.im)(hq:0≤q.im)(hzB:‖z‖≤B)(hqnorm:‖q‖≤2)
    (hA:0≤A)(hL:0≤L)(hε:0≤ε)(hKM:0≤KM)(hKA:0≤KA)
    (hrows:g.LocalCommonIncidenceRows T labels samples selector S q z KM KA)
    (hleaf:g.OmittedKeptLeafDecayControlled hd T labels samples selector S q z B C1 A L ε)
    (hnorm:g.OmittedKeptControlled hd T labels samples selector S q z B C1 ε) :
    let s:=g.admissibleState T labels samples
    let J:=s.OmittedOrdinaryLeaves selector S⊕s.OmittedExtraLeaves selector S
    letI:DecidableEq (s.OmittedCore selector S):=fun a b=>Classical.propDecidable (a=b)
    ∀u v:s.OmittedCore selector S,∀ri rj:ℕ,
      (∀l:J,(ri:ℕ∞)≤(g.omittedCommonModel T labels samples selector S).graph.edist u
        (s.omittedAllMate selector S (s.omittedKeptEmbedding selector S l))) →
      (∀l:J,(rj:ℕ∞)≤(g.omittedCommonModel T labels samples selector S).graph.edist v
        (s.omittedAllMate selector S (s.omittedKeptEmbedding selector S l))) →
      let ai:=omittedRestoredSpatialConstant d B A*L*physicalTransfer d z^ri+
        omittedRestoredErrorConstant d B C1 A*L*ε
      let aj:=omittedRestoredSpatialConstant d B A*L*physicalTransfer d z^rj+
        omittedRestoredErrorConstant d B C1 A*L*ε
      ‖(g.omittedKeptRestoredModel T labels samples selector S).extensionGreen q z u v-
        (g.omittedCommonModel T labels samples selector S).extensionGreen q z u v‖≤
      omittedNormalizationConstant d B C1*ε+(Fintype.card J:ℝ)*(B+2+(KM+KA))*ai*aj := by
  dsimp only
  let s:=g.admissibleState T labels samples
  let J:=s.OmittedOrdinaryLeaves selector S⊕s.OmittedExtraLeaves selector S
  letI:DecidableEq (s.OmittedCore selector S):=fun a b=>Classical.propDecidable (a=b)
  letI:DecidableEq J:=fun a b=>Classical.propDecidable (a=b)
  let C:=g.omittedCommonModel T labels samples selector S
  let mate:=s.omittedAllMate selector S ∘s.omittedKeptEmbedding selector S
  let H:=g.omittedKeptCompletion (by omega:1≤d) T labels samples selector S
  have hC:0≤finiteExtraReferenceConstant d:=by linarith [finiteExtraReferenceConstant_ge_one d hd]
  have hconv:=coreConvolutionConstant_nonnegative (finiteOmega d+1)
  have hsp:0≤omittedRestoredSpatialConstant d B A:=by unfold omittedRestoredSpatialConstant;positivity
  have her:0≤omittedRestoredErrorConstant d B C1 A:=by
    unfold omittedRestoredErrorConstant omittedNormalizationConstant omittedNormalizationCoefficient omittedKeptRowConstant
    positivity
  have hm:=g.localCommonRows_kept_mates T labels samples selector S q z KM KA hrows
  intro u v ri rj hri hrj
  let ai:=omittedRestoredSpatialConstant d B A*L*physicalTransfer d z^ri+
    omittedRestoredErrorConstant d B C1 A*L*ε
  let aj:=omittedRestoredSpatialConstant d B A*L*physicalTransfer d z^rj+
    omittedRestoredErrorConstant d B C1 A*L*ε
  have hρ:0≤physicalTransfer d z:=(physicalTransfer_pos d hd z).le
  have hai:0≤ai:=by dsimp only [ai];positivity
  have haj:0≤aj:=by dsimp only [aj];positivity
  have hx (l:J):‖H.extensionGreen q z (.inl u) (.inr l)‖≤ai:=hleaf u l ri (hri l)
  have hy (l:J):‖H.extensionGreen q z (.inr l) (.inl v)‖≤aj:=by
    have hs:=congrArg norm ((H.extensionGreen_isSymm q z).apply (.inl v) (.inr l))
    exact hs.trans_le (hleaf v l rj (hrj l))
  have hcmp:=C.attachLeaves_target_change_bound hd mate
    (g.omittedKeptMate_restore_budget T labels samples selector S) q z hz hq B (KM+KA) ai aj hzB hqnorm
    (add_nonneg hKM hKA) hai haj (fun l=>hm (mate l)) u v hx hy
  have hn:=hnorm.2.2 u v
  have ht:=norm_sub_le_norm_sub_add_norm_sub
    ((g.omittedKeptRestoredModel T labels samples selector S).extensionGreen q z u v)
    (H.extensionGreen q z (.inl u) (.inl v)) (C.extensionGreen q z u v)
  have hn' : ‖(g.omittedKeptRestoredModel T labels samples selector S).extensionGreen q z u v-
      H.extensionGreen q z (.inl u) (.inl v)‖≤omittedNormalizationConstant d B C1*ε := by
    rw [norm_sub_rev]
    exact hn
  exact ht.trans (add_le_add hn' hcmp)

end RegularGraph
end LocalLaw
