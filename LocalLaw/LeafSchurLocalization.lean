import LocalLaw.LeafSchurComparison
import LocalLaw.LeafPaddedLocalization

/-! # Localization of actual leaf-deleted model kernels

The asymmetric model localization is inserted into the exact leaf Schur
identity. Only the scalar leaf covariance and target-to-leaf weights remain
as finite inputs; the full and local leaf inverses and their corrections are
the actual model inverses.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2200000
namespace LocalLaw
local instance leafSchurLocalizationDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem scalar_leaf_subtype_contraction {I : Type} [Fintype I] (E : Set I) (p : ℂ) (δ : ℝ)
    (hδ : 0≤δ) (hsmall : (Fintype.card I:ℝ)*‖p⁻¹‖*δ≤1/2) :
    (Fintype.card E:ℝ)*‖p⁻¹‖*δ≤1/2 := by
  have hc : (Fintype.card E:ℝ)≤(Fintype.card I:ℝ) := by
    exact_mod_cast Fintype.card_le_of_injective (Subtype.val:E→I) Subtype.val_injective
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc (norm_nonneg _)) hδ).trans hsmall

namespace DeficientGraph
variable {V I : Type} [Fintype V] [Fintype I] {d : ℕ}

theorem attachLeaves_restriction_localization_bound (g : DeficientGraph V d) (hd : 3≤d)
    (mate : I→V) (hrestore : ∀v,multiLeafMultiplicity mate v≤g.deficit v)
    (S : Set V) (q z p : ℂ) (hz : 0<z.im) (hq : 0≤q.im) (hp : p≠0) :
    let H:=g.attachLeaves (by omega) mate hrestore
    let U:=multiLeafLift mate S
    let P:=H.extensionGreen q z
    let Q:=(H.restrict U).extensionGreen q z
    ∀(hbudget : H.ComponentFiniteReferenceBudget)(B : ℝ)(hzB : ‖z‖≤B)
    (ε L A : ℝ)(hε : 0≤ε)(hεOne : ε≤1)(hL : 1≤L)(hA : 0≤A)(hcap : ε*L^4≤1)
    (hprior : ‖q-semicircleRoot z‖≤scalarScale (spectralScale z) ε)
    (R Rs : ℕ)(hR : ∀a b,H.graph.dist a b≤R)(hRs : ∀a b,(H.restrict U).graph.dist a b≤Rs)
    (hRlog : (R:ℝ)+1≤A*L)(hRslog : (Rs:ℝ)+1≤A*L)
    (hlarge : localizationBudgetConstant d B A≤L)(i j : S)(r : ℕ)
    (hI : graphBallVertices H.graph (.inl i.val) r⊆U)
    (hJ : graphBallVertices H.graph (.inl j.val) r⊆U)
    (δleaf W : ℝ)(hδleaf : 0≤δleaf)(hW : 0≤W)
    (ha : (∑l:I,‖P (.inl i.val) (.inr l)‖)≤W)
    (hb : (∑l:I,‖P (.inr l) (.inl j.val)‖)≤W)
    (ha' : (∑l:{l:I //mate l∈S},‖Q (multiLeafLiftCore mate S i) (multiLeafLiftLeaf mate S l)‖)≤W)
    (hb' : (∑l:{l:I //mate l∈S},‖Q (multiLeafLiftLeaf mate S l) (multiLeafLiftCore mate S j)‖)≤W)
    (hPleaf : ∀l k:I,‖P (.inr l) (.inr k)-(if l=k then p else 0)‖≤δleaf)
    (hQleaf : ∀l k:{l:I //mate l∈S},‖Q (multiLeafLiftLeaf mate S l) (multiLeafLiftLeaf mate S k)-
      (if l=k then p else 0)‖≤δleaf)
    (hsmall : (Fintype.card I:ℝ)*‖p⁻¹‖*δleaf≤1/2),
    let u:=2*localizationFeedbackConstant d B A*L*ε
    let v:=localizationTailConstant d
    let C:=2*finiteExtraReferenceConstant d
    let ρ:=physicalTransfer d z
    ‖g.extensionGreen q z i.val j.val-(g.restrict S).extensionGreen q z i j‖≤
      u+v*ρ^(2*r)+‖p⁻¹‖*(2*u*W+(2*v*C+C^2)*(Fintype.card I:ℝ)*ρ^(2*r))+
        4*‖p⁻¹‖^2*δleaf*W^2 := by
  dsimp only
  intro hbudget B hzB ε L A hε hεOne hL hA hcap hprior R Rs hR hRs hRlog hRslog hlarge
    i j r hI hJ δleaf W hδleaf hW ha hb ha' hb' hPleaf hQleaf hsmall
  let H:=g.attachLeaves (by omega) mate hrestore
  let U:=multiLeafLift mate S
  let P:=H.extensionGreen q z
  let Q:=(H.restrict U).extensionGreen q z
  let u:=2*localizationFeedbackConstant d B A*L*ε
  let v:=localizationTailConstant d
  let C:=2*finiteExtraReferenceConstant d
  let ρ:=physicalTransfer d z
  have hxy:=H.componentwise_weak_restriction_localization_asymmetric hd hbudget U q z hz hq B hzB
    ε L A hε hεOne hL hA hcap hprior R Rs hR hRs hRlog hRslog hlarge
    (multiLeafLiftCore mate S i) (multiLeafLiftCore mate S j) r r hI hJ
  have hxy' : ‖P (.inl i.val) (.inl j.val)-Q (multiLeafLiftCore mate S i) (multiLeafLiftCore mate S j)‖≤
      u+v*ρ^(2*r) := by
    convert hxy using 1
    simp only [u,v,ρ,two_mul]
  have hlocalrow : (∑l:{l:I //(.inr l:V⊕I)∈U},
      ‖Q (multiLeafLiftCore mate S i) ⟨.inr l.val,l.property⟩‖)≤W := by
    convert ha' using 1
  have hproduct:=H.leaf_padded_localization_products hd hbudget U (Sum.inr:I→V⊕I)
    q z hz hq B hzB ε L A hε hεOne hL hA hcap hprior R Rs hR hRs hRlog hRslog hlarge
    (multiLeafLiftCore mate S i) (multiLeafLiftCore mate S j) r hI hJ W W hlocalrow hb
  let E : Set I:={l |mate l∈S}
  have hsmallF:=scalar_leaf_subtype_contraction E p δleaf hδleaf hsmall
  have hbase:=g.attachLeaves_restriction_schur_bound hd mate hrestore S q z p hz hq hp i j
    (u+v*ρ^(2*r)) δleaf W hδleaf hW hxy' ha hb ha' hb' hPleaf hQleaf hsmall hsmallF
  have hprod : (∑l:I,‖P (.inl i.val) (.inr l)*P (.inr l) (.inl j.val)-
      scalarLeafPaddedVector E
        (fun l=>Q (multiLeafLiftCore mate S i) (multiLeafLiftLeaf mate S l)) l *
      scalarLeafPaddedVector E
        (fun l=>Q (multiLeafLiftLeaf mate S l) (multiLeafLiftCore mate S j)) l‖)≤
      2*u*W+(2*v*C+C^2)*(Fintype.card I:ℝ)*ρ^(2*r) := by
    convert hproduct using 1
    ring
  exact hbase.trans (add_le_add_right
    (add_le_add_left (mul_le_mul_of_nonneg_left hprod (norm_nonneg _)) _) _)

end DeficientGraph
end LocalLaw
