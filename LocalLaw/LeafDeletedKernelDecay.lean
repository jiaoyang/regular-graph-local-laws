import LocalLaw.ComponentBoundaryKernelProduct
import LocalLaw.LeafSchurModelRows

/-! # Decay of a leaf-deleted core without a reference-class premise

The completed model has the proved finite reference class; its core need
not have that class. The actual virtual-leaf product is dominated by the
component-safe boundary convolution before taking its Schur correction.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2200000
namespace LocalLaw
local instance leafDeletedKernelDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace DeficientGraph
variable {V I : Type} [Fintype V] [Fintype I] {d : ℕ}

theorem attachLeaves_boundaryCoefficient_leaf_for_decay (g : DeficientGraph V d) (hd : 3≤d)
    (mate : I→V) (hrestore : ∀v,multiLeafMultiplicity mate v≤g.deficit v) (l : I) :
    (g.attachLeaves (by omega) mate hrestore).boundaryCoefficient (.inr l)=1 := by
  have hD : (3:ℝ)≤d := Nat.cast_le.mpr hd
  have hdeg:=multiLeafGraph_degree_leaf g.graph mate l
  simp only [←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] at hdeg
  have hδ : (g.attachLeaves (by omega) mate hrestore).deficit (.inr l)=0 := rfl
  unfold boundaryCoefficient
  simp only [hδ,Nat.cast_zero,sub_zero,←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card]
  rw [show Nat.card ((g.attachLeaves (by omega) mate hrestore).graph.neighborSet (.inr l))=1 from hdeg]
  simp only [Nat.cast_one]
  exact div_self (by linarith)

theorem attachLeaves_leaf_product_sum_bound (g : DeficientGraph V d) (hd : 3≤d)
    (mate : I→V) (hrestore : ∀v,multiLeafMultiplicity mate v≤g.deficit v)
    (q z : ℂ) (hz : 0<z.im) (hq : 0≤q.im) :
    let H:=g.attachLeaves (by omega) mate hrestore
    ∀(hb : H.ComponentFiniteReferenceBudget)(R : ℕ)(hR : ∀a b,H.graph.dist a b≤R)
    (small : ‖q-semicircleRoot z‖*finiteExtraReferenceConstant d*
      coreConvolutionConstant (finiteOmega d+1)*((R:ℝ)+1)≤1/2)
    (x y : V)(h : ℕ)(hfar : (h:ℕ∞)≤g.graph.edist x y),
    (∑l:I,‖H.extensionGreen q z (.inl x) (.inr l)*H.extensionGreen q z (.inr l) (.inl y)‖)≤
      (2*finiteExtraReferenceConstant d)^2*coreConvolutionConstant (finiteOmega d+1)*
        ((R:ℝ)+1)*physicalTransfer d z^h := by
  dsimp only
  intro hb R hR small x y h hfar
  let H:=g.attachLeaves (by omega) mate hrestore
  let e:I↪(V⊕I):={toFun:=Sum.inr,inj':=Sum.inr_injective}
  have hfarH : (h:ℕ∞)≤H.graph.edist (.inl x) (.inl y) := by
    change (h:ℕ∞)≤(multiLeafGraph g.graph mate).edist (.inl x) (.inl y)
    rw [multiLeafGraph_edist_old]
    exact hfar
  exact H.weight_one_boundary_kernel_product hd hb e
    (g.attachLeaves_boundaryCoefficient_leaf_for_decay hd mate hrestore) q z hz hq R hR small (.inl x) (.inl y) h hfarH

theorem attachLeaves_core_edist_decay (g : DeficientGraph V d) (hd : 3≤d)
    (mate : I→V) (hrestore : ∀v,multiLeafMultiplicity mate v≤g.deficit v)
    (q z p : ℂ) (hz : 0<z.im) (hq : 0≤q.im) (hp : p≠0) :
    let H:=g.attachLeaves (by omega) mate hrestore
    ∀(hb : H.ComponentFiniteReferenceBudget)(R : ℕ)(hR : ∀a b,H.graph.dist a b≤R)
    (small : ‖q-semicircleRoot z‖*finiteExtraReferenceConstant d*
      coreConvolutionConstant (finiteOmega d+1)*((R:ℝ)+1)≤1/2)
    (δ W : ℝ)(hδ : 0≤δ)(hW : 0≤W)
    (herror : ∀l k:I,‖H.extensionGreen q z (.inr l) (.inr k)-(if l=k then p else 0)‖≤δ)
    (hsmall : (Fintype.card I:ℝ)*‖p⁻¹‖*δ≤1/2)
    (hrows : ∀x:V,(∑l:I,‖H.extensionGreen q z (.inl x) (.inr l)‖)≤W)
    (x y : V)(h : ℕ)(hfar : (h:ℕ∞)≤g.graph.edist x y),
    ‖g.extensionGreen q z x y‖≤
      (2*finiteExtraReferenceConstant d+‖p⁻¹‖*(2*finiteExtraReferenceConstant d)^2*
        coreConvolutionConstant (finiteOmega d+1)*((R:ℝ)+1))*physicalTransfer d z^h+
        2*‖p⁻¹‖^2*δ*W^2 := by
  dsimp only
  intro hb R hR small δ W hδ hW herror hsmall hrows x y h hfar
  let H:=g.attachLeaves (by omega) mate hrestore
  let M:=H.extensionMatrix q z
  have hM:IsUnit M:=H.extensionMatrix_isUnit hd q z hz hq
  have hcore:M.toBlocks₁₁=g.extensionMatrix q z:=
    g.attachLeaves_extensionMatrix_principal (by omega) mate hrestore q z
  have hc:IsUnit M.toBlocks₁₁:=hcore ▸ g.extensionMatrix_isUnit hd q z hz hq
  have hi:=scalar_diagonal_inverse_stability (M⁻¹).toBlocks₂₂ p hp
    (core_inverse_leaf_schur M hM hc).1 δ hδ herror hsmall
  have hcol : (∑l:I,‖H.extensionGreen q z (.inr l) (.inl y)‖)≤W := by
    simpa only [(H.extensionGreen_isSymm q z).apply] using hrows y
  have hfarH : (h:ℕ∞)≤H.graph.edist (.inl x) (.inl y) := by
    change (h:ℕ∞)≤(multiLeafGraph g.graph mate).edist (.inl x) (.inl y)
    rw [multiLeafGraph_edist_old]
    exact hfar
  have hbase:=H.perturbed_green_edist_bound hd hb z q hz hq R hR small (.inl x) (.inl y) h hfarH
  have hproducts:=g.attachLeaves_leaf_product_sum_bound hd mate hrestore q z hz hq hb R hR small x y h hfar
  have hout:=core_inverse_leaf_entry_bound M hM hc x y p (2*‖p⁻¹‖^2*δ) W W
    (2*finiteExtraReferenceConstant d*physicalTransfer d z^h)
    ((2*finiteExtraReferenceConstant d)^2*coreConvolutionConstant (finiteOmega d+1)*((R:ℝ)+1)*physicalTransfer d z^h)
    (by positivity) hW hW (hrows x) hcol hi hbase hproducts
  rw [hcore] at hout
  convert hout using 1
  ring

end DeficientGraph
end LocalLaw
