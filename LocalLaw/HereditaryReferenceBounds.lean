import LocalLaw.HereditaryDiameter
import LocalLaw.ComponentRestrictionBudget
import LocalLaw.ComponentFiniteLipschitz

/-! # Perturbed reference bounds on arbitrary retained subsets

No ball-capture assumption is required: the original component budget and
ambient intrinsic diameter supply the restricted intrinsic diameter, while
the finite class itself is hereditary under arbitrary vertex restriction.
-/

noncomputable section
set_option maxHeartbeats 300000
namespace LocalLaw
local instance hereditaryReferenceDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def hereditaryReferenceRadius (d D : ℕ) : ℕ := (finiteOmega d+2)*(2*D+1)

namespace DeficientGraph
variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

theorem finite_class_restriction_intrinsic_diameter (g : DeficientGraph V d)
    (hbudget : g.ComponentFiniteReferenceBudget) (D : ℕ) (hD : ∀a b,g.graph.dist a b≤D)
    (S : Set V) (a b : S) : (g.restrict S).graph.dist a b≤hereditaryReferenceRadius d D := by
  have hΩ : ∀C:g.graph.ConnectedComponent,graphExcess (g.graph.induce C.supp)≤finiteOmega d+1 := by
    intro C
    simp only [graphExcess,SimpleGraph.edgeFinset_card,←Nat.card_eq_fintype_card]
    letI : DecidablePred (fun v:V => v∈C.supp) := fun _ => Classical.propDecidable _
    have h:=(hbudget C).complexity_le
    have he : graphExcess (g.restrict C.supp).graph≤finiteOmega d+1 := by omega
    simpa only [graphExcess,SimpleGraph.edgeFinset_card,←Nat.card_eq_fintype_card] using he
  exact componentwise_induce_intrinsic_diameter g.graph (finiteOmega d+1) D hΩ hD S a b

/-- Actual decay in every restriction, with a single explicit smallness
budget involving only the ambient diameter and finite reference threshold. -/
theorem hereditary_restriction_kernel_decay (g : DeficientGraph V d) (hd : 3≤d)
    (hbudget : g.ComponentFiniteReferenceBudget) (D : ℕ) (hD : ∀a b,g.graph.dist a b≤D)
    (S : Set V) (q z : ℂ) (hz : 0<z.im) (hq : 0≤q.im)
    (small : ‖q-semicircleRoot z‖*finiteExtraReferenceConstant d*
      coreConvolutionConstant (finiteOmega d+1)*((hereditaryReferenceRadius d D:ℝ)+1)≤1/2)
    (a b : S) :
    ‖(g.restrict S).extensionGreen q z a b‖≤
      2*finiteExtraReferenceConstant d*physicalTransfer d z^((g.restrict S).graph.dist a b) := by
  exact (g.restrict S).componentwise_finite_kernel_decay hd
    (g.restrict_componentFiniteReferenceBudget S hbudget) q z hz hq
    (hereditaryReferenceRadius d D) (g.finite_class_restriction_intrinsic_diameter hbudget D hD S)
    small a b

theorem hereditary_restriction_entry_bound (g : DeficientGraph V d) (hd : 3≤d)
    (hbudget : g.ComponentFiniteReferenceBudget) (D : ℕ) (hD : ∀a b,g.graph.dist a b≤D)
    (S : Set V) (q z : ℂ) (hz : 0<z.im) (hq : 0≤q.im)
    (small : ‖q-semicircleRoot z‖*finiteExtraReferenceConstant d*
      coreConvolutionConstant (finiteOmega d+1)*((hereditaryReferenceRadius d D:ℝ)+1)≤1/2)
    (a b : S) : ‖(g.restrict S).extensionGreen q z a b‖≤2*finiteExtraReferenceConstant d := by
  have h:=g.hereditary_restriction_kernel_decay hd hbudget D hD S q z hz hq small a b
  have hρ : 0≤physicalTransfer d z := (physicalTransfer_pos d hd z).le
  have hρ1 : physicalTransfer d z≤1 := by nlinarith [physicalTransfer_sq_le_half d hd z]
  have hC : 0≤2*finiteExtraReferenceConstant d := by
    have hc:=finiteExtraReferenceConstant_ge_one d hd
    positivity
  exact h.trans (mul_le_of_le_one_right hC (pow_le_one₀ hρ hρ1))

theorem hereditary_restriction_uniform_lipschitz (g : DeficientGraph V d) (hd : 3≤d)
    (hbudget : g.ComponentFiniteReferenceBudget) (D : ℕ) (hD : ∀a b,g.graph.dist a b≤D)
    (S : Set V) (z q v : ℂ) (hz : 0<z.im) (hq : 0≤q.im) (hv : 0≤v.im)
    (smallq : ‖q-semicircleRoot z‖*finiteExtraReferenceConstant d*
      coreConvolutionConstant (finiteOmega d+1)*((hereditaryReferenceRadius d D:ℝ)+1)≤1/2)
    (smallv : ‖v-semicircleRoot z‖*finiteExtraReferenceConstant d*
      coreConvolutionConstant (finiteOmega d+1)*((hereditaryReferenceRadius d D:ℝ)+1)≤1/2)
    (a b : S) :
    ‖(g.restrict S).extensionGreen q z a b-(g.restrict S).extensionGreen v z a b‖≤
      (16*finiteExtraReferenceConstant d^2*coreConvolutionConstant (finiteOmega d+1))*‖q-v‖ := by
  exact (g.restrict S).componentwise_finite_uniform_lipschitz hd
    (g.restrict_componentFiniteReferenceBudget S hbudget) z q v hz hq hv
    (hereditaryReferenceRadius d D) (g.finite_class_restriction_intrinsic_diameter hbudget D hD S)
    smallq smallv a b

end DeficientGraph
end LocalLaw
