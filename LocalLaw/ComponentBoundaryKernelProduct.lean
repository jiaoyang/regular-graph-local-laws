import LocalLaw.ComponentFiniteLocalization
import LocalLaw.LeafSchurLocalization

/-! # Component-safe convolution of actual perturbed model kernels

Products outside the root component vanish before any natural graph
distance is used. On the actual component, the inverse block, boundary
coefficient and metric agree with the ambient ones, and graph B.6 applies.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2200000
namespace LocalLaw
local instance componentBoundaryProductDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance (priority := high) componentBoundaryProductMemDecidable
    {A : Type*} (G : SimpleGraph A) (c : G.ConnectedComponent) :
    DecidablePred (fun a=>a∈c.supp) := fun _=>Classical.propDecidable _
namespace DeficientGraph
variable {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] {d : ℕ}

theorem component_boundary_kernel_product (g : DeficientGraph V d) (hd : 3≤d)
    (hb : g.ComponentFiniteReferenceBudget) (q z : ℂ) (hz : 0<z.im) (hq : 0≤q.im)
    (R : ℕ) (hR : ∀a b,g.graph.dist a b≤R)
    (small : ‖q-semicircleRoot z‖*finiteExtraReferenceConstant d*
      coreConvolutionConstant (finiteOmega d+1)*((R:ℝ)+1)≤1/2)
    (x y : V) (h : ℕ) (hfar : (h:ℕ∞)≤g.graph.edist x y) :
    (∑v:V,g.boundaryCoefficient v*‖g.extensionGreen q z x v‖*‖g.extensionGreen q z v y‖)≤
      (2*finiteExtraReferenceConstant d)^2*coreConvolutionConstant (finiteOmega d+1)*
        ((R:ℝ)+1)*physicalTransfer d z^h := by
  let C:=g.graph.connectedComponentMk x
  let M:=g.restrict C.supp
  let t:=physicalTransfer d z
  let K:=2*finiteExtraReferenceConstant d
  have ht0 : 0≤t := (physicalTransfer_pos d hd z).le
  have ht1 : t≤1 := by dsimp only [t]; nlinarith [physicalTransfer_sq_le_half d hd z]
  have hK : 0≤K := by dsimp only [K]; linarith [finiteExtraReferenceConstant_ge_one d hd]
  have hconv0:=coreConvolutionConstant_nonnegative (finiteOmega d+1)
  have hnonneg : ∀v,g.boundaryCoefficient v*‖g.extensionGreen q z x v‖*‖g.extensionGreen q z v y‖≥0 :=
    fun v=>mul_nonneg (mul_nonneg (g.boundaryCoefficient_nonnegative hd v) (norm_nonneg _)) (norm_nonneg _)
  by_cases hy:y∈C.supp
  · let xx:C.supp:=⟨x,rfl⟩
    let yy:C.supp:=⟨y,hy⟩
    have hconn : M.graph.Connected := C.connected_induce_supp
    have hdiam : ∀a b,M.graph.dist a b≤R := by
      intro a b
      change (g.graph.induce C.supp).dist a b≤R
      rw [isolated_induce_distance g.graph C.supp (g.component_cut C)]
      exact hR a.val b.val
    have hbM : M.FiniteReferenceBudget := hb C
    have hω : graphExcess M.graph≤finiteOmega d+1 := by have hh:=hbM.complexity_le;omega
    have hk:=M.finite_class_kernel_bound hd hconn (hb C) z q hz hq R hdiam small
    have hcomponent : (∑v:V,g.boundaryCoefficient v*‖g.extensionGreen q z x v‖*‖g.extensionGreen q z v y‖)=
        ∑v:C.supp,M.boundaryCoefficient v*‖M.extensionGreen q z xx v‖*‖M.extensionGreen q z v yy‖ := by
      have hs:=Fintype.sum_subtype_add_sum_subtype (fun v:V=>v∈C.supp)
        (fun v=>g.boundaryCoefficient v*‖g.extensionGreen q z x v‖*‖g.extensionGreen q z v y‖)
      have hzout : (∑v:{v:V //v∉C.supp},g.boundaryCoefficient v.val*
          ‖g.extensionGreen q z x v.val‖*‖g.extensionGreen q z v.val y‖)=0 := by
        apply Finset.sum_eq_zero
        intro v _
        rw [g.extensionGreen_zero_across_cut hd C.supp (g.component_cut C) q z hz hq x rfl v.val v.property]
        simp
      simp only [←finsum_eq_sum_of_fintype] at hs hzout ⊢
      rw [←hs,hzout,add_zero]
      apply finsum_congr
      intro v
      rw [g.restrict_boundaryCoefficient_of_isolated C.supp (g.component_cut C)]
      have hgreen:=g.restrict_extensionGreen_of_isolated hd C.supp (g.component_cut C) q z hz hq
      rw [hgreen]
      rfl
    have hprod : (∑v:C.supp,M.boundaryCoefficient v*‖M.extensionGreen q z xx v‖*‖M.extensionGreen q z v yy‖)≤
        K^2*∑v:C.supp,M.boundaryCoefficient v*M.referenceDecay z xx v*M.referenceDecay z v yy := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro v _
      have ha:=hk xx v
      have hb':=hk v yy
      calc
        _≤M.boundaryCoefficient v*(K*M.referenceDecay z xx v)*(K*M.referenceDecay z v yy) :=
          mul_le_mul (mul_le_mul_of_nonneg_left ha (M.boundaryCoefficient_nonnegative hd v)) hb'
            (norm_nonneg _) (mul_nonneg (M.boundaryCoefficient_nonnegative hd v)
              (mul_nonneg hK (M.referenceDecay_pos hd z xx v).le))
        _=_ := by ring
    have hc:=M.referenceDecay_convolution hd hconn (finiteOmega d+1) hω z xx yy
    have hdxy : M.graph.dist xx yy=g.graph.dist x y :=
      isolated_induce_distance g.graph C.supp (g.component_cut C) xx yy
    have hnat : h≤g.graph.dist x y := by
      have hr:g.graph.Reachable x y:=SimpleGraph.ConnectedComponent.exact hy.symm
      have he:(g.graph.dist x y:ℕ∞)=g.graph.edist x y:=ENat.coe_toNat (SimpleGraph.edist_ne_top_iff_reachable.mpr hr)
      exact ENat.coe_le_coe.mp (hfar.trans_eq he.symm)
    calc
      _≤K^2*(coreConvolutionConstant (finiteOmega d+1)*M.referenceCompanion z xx yy) := by
        rw [hcomponent]
        exact hprod.trans (mul_le_mul_of_nonneg_left hc (sq_nonneg _))
      _≤K^2*(coreConvolutionConstant (finiteOmega d+1)*(((R:ℝ)+1)*t^(g.graph.dist x y))) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        apply mul_le_mul_of_nonneg_left _ hconv0
        simpa only [referenceDecay,t,hdxy] using M.referenceCompanion_diameter_bound hd z R hdiam xx yy
      _≤K^2*(coreConvolutionConstant (finiteOmega d+1)*(((R:ℝ)+1)*t^h)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one ht0 ht1 hnat) (by positivity)) hconv0)
          (sq_nonneg _)
      _=_ := by dsimp only [K,t];ring
  · have hzero : (∑v:V,g.boundaryCoefficient v*‖g.extensionGreen q z x v‖*‖g.extensionGreen q z v y‖)=0 := by
      apply Finset.sum_eq_zero
      intro v _
      by_cases hv:v∈C.supp
      · rw [g.extensionGreen_zero_across_cut hd C.supp (g.component_cut C) q z hz hq v hv y hy]
        simp
      · rw [g.extensionGreen_zero_across_cut hd C.supp (g.component_cut C) q z hz hq x rfl v hv]
        simp
    rw [hzero]
    positivity

/-- A genuine injectively labelled weight-one boundary subset is bounded
by the actual nonnegative boundary convolution. -/
theorem weight_one_boundary_kernel_product (g : DeficientGraph V d) (hd : 3≤d)
    (hb : g.ComponentFiniteReferenceBudget) (e : I↪V) (he : ∀l,g.boundaryCoefficient (e l)=1)
    (q z : ℂ) (hz : 0<z.im) (hq : 0≤q.im) (R : ℕ) (hR : ∀a b,g.graph.dist a b≤R)
    (small : ‖q-semicircleRoot z‖*finiteExtraReferenceConstant d*
      coreConvolutionConstant (finiteOmega d+1)*((R:ℝ)+1)≤1/2)
    (x y : V) (h : ℕ) (hfar : (h:ℕ∞)≤g.graph.edist x y) :
    (∑l:I,‖g.extensionGreen q z x (e l)*g.extensionGreen q z (e l) y‖)≤
      (2*finiteExtraReferenceConstant d)^2*coreConvolutionConstant (finiteOmega d+1)*
        ((R:ℝ)+1)*physicalTransfer d z^h := by
  have hf : ∀v,0≤g.boundaryCoefficient v*‖g.extensionGreen q z x v‖*‖g.extensionGreen q z v y‖ :=
    fun v=>mul_nonneg (mul_nonneg (g.boundaryCoefficient_nonnegative hd v) (norm_nonneg _)) (norm_nonneg _)
  calc
    _=∑l:I,g.boundaryCoefficient (e l)*‖g.extensionGreen q z x (e l)‖*‖g.extensionGreen q z (e l) y‖ := by
      simp only [he,one_mul,norm_mul]
    _=∑v∈Finset.univ.image e,g.boundaryCoefficient v*‖g.extensionGreen q z x v‖*‖g.extensionGreen q z v y‖ := by
      rw [Finset.sum_image]
      intro a _ b _ h
      exact e.injective h
    _≤∑v:V,g.boundaryCoefficient v*‖g.extensionGreen q z x v‖*‖g.extensionGreen q z v y‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun v _ _=>hf v)
    _≤_ := g.component_boundary_kernel_product hd hb q z hz hq R hR small x y h hfar

end DeficientGraph
end LocalLaw
