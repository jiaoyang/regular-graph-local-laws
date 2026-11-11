import LocalLaw.AttachedLeafSubfamilyRows
import LocalLaw.ComponentBoundaryKernelProduct
import LocalLaw.NormalizedLeafPrecision

/-! # Intrinsic core decay after deleting only a leaf complement

The completed model supplies the class. A scalar covariance Schur inverse
and its actual weight-one boundary convolution control the deleted core;
no finite-class statement for that core or for the kept model is assumed.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 3500000
namespace LocalLaw
local instance attachedLeafSubfamilyGeneralDecayDecidable (p : Prop) : Decidable p := Classical.propDecidable p
@[simp] theorem leafBlockPartition_retained {V L J:Type}[Fintype J](e:J↪L)(v:V⊕J) :
    leafBlockPartition (V:=V) e (.inl v)=Sum.map id e v := by
  cases v <;> rfl

namespace DeficientGraph
variable {V L J : Type}[Fintype V][Fintype L][Fintype J]{d : ℕ}

theorem attachLeaves_subfamily_general_decay (g : DeficientGraph V d)(hd : 3≤d)(mate : L→V)
    (hr : ∀v,multiLeafMultiplicity mate v≤g.deficit v)(e : J↪L)(q z p : ℂ)
    (hz : 0<z.im)(hq : 0≤q.im)(hp : p≠0) :
    let H := g.attachLeaves (by omega) mate hr
    ∀(hb : H.ComponentFiniteReferenceBudget)(R : ℕ)(hR : ∀a b,H.graph.dist a b≤R)
    (small : ‖q-semicircleRoot z‖*finiteExtraReferenceConstant d*
      coreConvolutionConstant (finiteOmega d+1)*((R:ℝ)+1)≤1/2)
    (δ W : ℝ)(hδ : 0≤δ)(hW : 0≤W)
    (herror : ∀l k:LeafFamilyComplement e,
      ‖H.extensionGreen q z (.inr l.val) (.inr k.val)-(if l=k then p else 0)‖≤δ)
    (hsmall : (Fintype.card (LeafFamilyComplement e):ℝ)*‖p⁻¹‖*δ≤1/2)
    (hrows : ∀x:V⊕L,∑l:L,‖H.extensionGreen q z x (.inr l)‖≤W)
    (x y : V⊕J)(h : ℕ)(hfar : (h:ℕ∞)≤
      (multiLeafGraph g.graph mate).edist (Sum.map id e x) (Sum.map id e y)),
    let kept := g.attachLeaves (by omega) (mate∘e)
      (fun v => (subfamily_leaf_multiplicity_le mate e v).trans (hr v))
    ‖kept.extensionGreen q z x y‖≤
      (2*finiteExtraReferenceConstant d+‖p⁻¹‖*(2*finiteExtraReferenceConstant d)^2*
        coreConvolutionConstant (finiteOmega d+1)*((R:ℝ)+1))*physicalTransfer d z^h+
        2*‖p⁻¹‖^2*δ*W^2 := by
  dsimp only
  intro hb R hR small δ W hδ hW herror hsmall hrows x y h hfar
  let H := g.attachLeaves (by omega) mate hr
  let M := g.leafSubfamilyMatrix hd mate hr e q z
  let f := leafBlockPartition (V:=V) e
  let C := 2*finiteExtraReferenceConstant d
  let T := C^2*coreConvolutionConstant (finiteOmega d+1)*((R:ℝ)+1)
  have hi (a b:(V⊕J)⊕LeafFamilyComplement e) : M⁻¹ a b=H.extensionGreen q z (f a) (f b) :=
    congrArg (fun P => P a b) (g.leafSubfamilyMatrix_inverse hd mate hr e q z)
  have hu := g.leafSubfamilyMatrix_units hd mate hr e q z hz hq
  have he : ∀l k:LeafFamilyComplement e,
      ‖M⁻¹ (.inr l) (.inr k)-(if l=k then p else 0)‖≤δ := by
    intro l k
    simpa only [hi,f,leafBlockPartition_removed] using herror l k
  have hInv := scalar_diagonal_inverse_stability (M⁻¹).toBlocks₂₂ p hp
    (core_inverse_leaf_schur M hu.1 hu.2).1 δ hδ he hsmall
  have hfarH : (h:ℕ∞)≤H.graph.edist (Sum.map id e x) (Sum.map id e y) := hfar
  have hbase : ‖M⁻¹ (.inl x) (.inl y)‖≤C*physicalTransfer d z^h := by
    simpa only [hi,f,leafBlockPartition_retained,C] using
      H.perturbed_green_edist_bound hd hb z q hz hq R hR small (Sum.map id e x) (Sum.map id e y) h hfarH
  have hrow (v:V⊕J) : (∑l:LeafFamilyComplement e,‖M⁻¹ (.inl v) (.inr l)‖)≤W := by
    simpa only [hi,f,leafBlockPartition_retained,leafBlockPartition_removed] using
      (finite_norm_sum_embedding_le (Function.Embedding.subtype (fun l:L => l∉Set.range e))
        (fun l => H.extensionGreen q z (Sum.map id e v) (.inr l))).trans (hrows (Sum.map id e v))
  have hMsym : (M⁻¹).IsSymm := by
    rw [g.leafSubfamilyMatrix_inverse hd mate hr e q z]
    exact (H.extensionGreen_isSymm q z).submatrix f
  have hcol : (∑l:LeafFamilyComplement e,‖M⁻¹ (.inr l) (.inl y)‖)≤W := by
    calc
      _ = ∑l:LeafFamilyComplement e,‖M⁻¹ (.inl y) (.inr l)‖ := by
        apply Finset.sum_congr rfl
        intro l _
        exact congrArg norm (hMsym.apply (.inl y) (.inr l))
      _ ≤ _ := hrow y
  let er : LeafFamilyComplement e ↪ V⊕L :=
    {toFun := fun l => .inr l.val,inj' := fun _ _ h => Subtype.ext (Sum.inr.inj h)}
  have hprod : (∑l:LeafFamilyComplement e,
      ‖M⁻¹ (.inl x) (.inr l)*M⁻¹ (.inr l) (.inl y)‖)≤T*physicalTransfer d z^h := by
    have hh := H.weight_one_boundary_kernel_product hd hb er
      (fun l => g.attachLeaves_boundaryCoefficient_leaf hd mate hr l.val) q z hz hq R hR small
      (Sum.map id e x) (Sum.map id e y) h hfarH
    simpa only [hi,f,leafBlockPartition_retained,leafBlockPartition_removed,T,C,er,Function.Embedding.coeFn_mk] using hh
  have hh := core_inverse_leaf_entry_bound M hu.1 hu.2 x y p
    (2*‖p⁻¹‖^2*δ) W W (C*physicalTransfer d z^h) (T*physicalTransfer d z^h)
    (by positivity) hW hW (hrow x) hcol hInv hbase hprod
  rw [g.leafSubfamilyMatrix_core hd mate hr e q z] at hh
  convert hh using 1
  dsimp only [T,C]
  ring

end DeficientGraph
end LocalLaw
