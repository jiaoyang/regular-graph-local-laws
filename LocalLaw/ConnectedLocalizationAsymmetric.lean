import LocalLaw.FiniteLocalizationAsymmetric
import LocalLaw.CapturedBallComponents
import LocalLaw.DeficientGraphIso

/-! # Asymmetric localization into a possibly disconnected retained set -/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1800000
namespace LocalLaw
local instance connectedLocalizationAsymmetricDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance (priority := high) connectedLocalizationAsymComponentDecidable
    {A : Type*} (H : SimpleGraph A) (C : H.ConnectedComponent) :
    DecidablePred (fun a=>a∈C.supp) := fun _=>Classical.propDecidable _
namespace DeficientGraph
variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

def asymmetricLocalizationBound (d : ℕ) (q z : ℂ) (B : ℝ) (R ri rj : ℕ) : ℝ :=
  32*finiteExtraReferenceConstant d^2*coreConvolutionConstant (finiteOmega d+1)*ordinaryFeedbackBudget z q B R+
    (8*finiteExtraReferenceConstant d^2*localizationExceptionalMass d q+
      4*finiteExtraReferenceConstant d^2*‖q‖*(((finiteOmega d:ℝ)+1)/((d:ℝ)-1))+
      2*finiteExtraReferenceConstant d)*physicalTransfer d z^(ri+rj)

theorem connected_restriction_localization_asymmetric (g : DeficientGraph V d) (hd : 3≤d)
    (hG : g.graph.Connected) (hbudget : g.FiniteReferenceBudget) (S : Set V)
    (q z : ℂ) (hz : 0<z.im) (hq : 0 ≤ q.im) (B : ℝ) (hzB : ‖z‖≤B)
    (R Rs : ℕ) (hR : ∀ a b,g.graph.dist a b≤R) (hRs : ∀ a b,(g.restrict S).graph.dist a b≤Rs)
    (smallG : ‖q-semicircleRoot z‖*finiteExtraReferenceConstant d*
      coreConvolutionConstant (finiteOmega d+1)*((R:ℝ)+1)≤1/2)
    (smallS : ‖q-semicircleRoot z‖*finiteExtraReferenceConstant d*
      coreConvolutionConstant (finiteOmega d+1)*((Rs:ℝ)+1)≤1/2)
    (smallOutside : ‖q-semicircleRoot z‖*finiteExtraReferenceConstant d*
      coreConvolutionConstant (finiteOmega d+1)*(((finiteOmega d+1)*(2*R+1):ℕ)+1:ℝ)≤1/2)
    (smallCavity : ‖q-semicircleRoot z‖*3*(3/2:ℝ)*((2*R:ℕ)+1:ℝ)≤1/2)
    (smallOrdinary : ordinaryFeedbackBudget z q B R*(2*finiteExtraReferenceConstant d)*
      coreConvolutionConstant (finiteOmega d+1)*((Rs:ℝ)+1)≤1/2)
    (i j : S) (ri rj : ℕ)
    (hI : graphBallVertices g.graph i.val ri⊆S) (hJ : graphBallVertices g.graph j.val rj⊆S) :
    ‖g.extensionGreen q z i.val j.val-(g.restrict S).extensionGreen q z i j‖≤
      asymmetricLocalizationBound d q z B R ri rj := by
  let M:=g.restrict S
  have hC : 0≤finiteExtraReferenceConstant d := (by norm_num : (0:ℝ)≤1).trans (finiteExtraReferenceConstant_ge_one d hd)
  have ht : 0≤physicalTransfer d z := (physicalTransfer_pos d hd z).le
  have ht1 : physicalTransfer d z≤1 := by nlinarith [physicalTransfer_sq_le_half d hd z]
  have htail : 0≤2*finiteExtraReferenceConstant d*physicalTransfer d z^(ri+rj) := by positivity
  by_cases hr : M.graph.Reachable i j
  · let C:=M.graph.connectedComponentMk i
    let K:=inducedComponentVertices g.graph S C
    let e:=inducedComponentIso g.graph S C
    let ii : C.supp:=⟨i,rfl⟩
    let jj : C.supp:=⟨j,(SimpleGraph.ConnectedComponent.sound hr).symm⟩
    have hKconn : (g.graph.induce K).Connected := e.connected_iff.mp C.connected_induce_supp
    have hKdiam (a b : K) : (g.restrict K).graph.dist a b≤Rs := by
      have hh : (M.graph.induce C.supp).dist (e.symm a) (e.symm b)≤Rs := by
        rw [isolated_induce_distance M.graph C.supp (M.component_cut C)]
        exact hRs (e.symm a).val (e.symm b).val
      have he:=graphIso_dist e (e.symm a) (e.symm b)
      simpa only [e.apply_symm_apply] using he.trans_le hh
    have hKI : graphBallVertices g.graph (e ii).val ri⊆K :=
      captured_ball_in_component g.graph S C i rfl ri hI
    have hKJ : graphBallVertices g.graph (e jj).val rj⊆K :=
      captured_ball_in_component g.graph S C j jj.property rj hJ
    have hh:=g.finite_model_localization_asymmetric hd K hG hKconn hbudget q z hz hq B hzB
      R Rs hR hKdiam smallG smallS smallOutside smallCavity smallOrdinary (e ii) (e jj) ri rj hKI hKJ
    have hIso:=(g.restrict K).extensionGreen_iso (M.restrict C.supp) e (fun _=>rfl) q z
    have hComp:=M.restrict_extensionGreen_of_isolated hd C.supp (M.component_cut C) q z hz hq
    have hmatch : (g.restrict K).extensionGreen q z (e ii) (e jj)=M.extensionGreen q z i j :=
      (congrArg (fun A : Matrix C.supp C.supp ℂ=>A ii jj) hIso).trans
        (congrArg (fun A : Matrix C.supp C.supp ℂ=>A ii jj) hComp)
    change ‖g.extensionGreen q z i.val j.val-(g.restrict K).extensionGreen q z (e ii) (e jj)‖≤_ at hh
    rw [hmatch] at hh
    apply hh.trans
    unfold asymmetricLocalizationBound
    nlinarith only [htail]
  · let C:=M.graph.connectedComponentMk i
    have hj : j∉C.supp := fun h=>hr (SimpleGraph.ConnectedComponent.exact h.symm)
    have hzlocal:=M.extensionGreen_zero_across_cut hd C.supp (M.component_cut C) q z hz hq i rfl j hj
    change ‖g.extensionGreen q z i.val j.val-M.extensionGreen q z i j‖≤_
    rw [hzlocal,sub_zero]
    have hdist:=captured_balls_disconnected_distance g.graph hG S i j ri rj hI hJ hr
    have hkernel:=g.finite_class_kernel_bound hd hG hbudget z q hz hq R hR smallG i.val j.val
    have hdecay:=pow_le_pow_of_le_one ht ht1 (show ri+rj≤g.graph.dist i.val j.val by omega)
    have hbound:=hkernel.trans (mul_le_mul_of_nonneg_left hdecay (by positivity : 0≤2*finiteExtraReferenceConstant d))
    apply hbound.trans
    have hτ:=ordinaryFeedbackBudget_nonnegative z q B R
    have hC0:=coreConvolutionConstant_nonnegative (finiteOmega d+1)
    have hmass : 0≤localizationExceptionalMass d q := by
      have hdR : (3:ℝ)≤d := Nat.cast_le.mpr hd
      unfold localizationExceptionalMass
      exact div_nonneg (by positivity) (by linarith)
    have hratio : 0≤((finiteOmega d:ℝ)+1)/((d:ℝ)-1) := by
      have hdR : (3:ℝ)≤d := Nat.cast_le.mpr hd
      exact div_nonneg (by positivity) (by linarith)
    unfold asymmetricLocalizationBound
    nlinarith only [mul_nonneg (show 0≤32*finiteExtraReferenceConstant d^2*coreConvolutionConstant (finiteOmega d+1) by positivity) hτ,
      mul_nonneg (show 0≤8*finiteExtraReferenceConstant d^2*localizationExceptionalMass d q+
        4*finiteExtraReferenceConstant d^2*‖q‖*(((finiteOmega d:ℝ)+1)/((d:ℝ)-1)) by positivity) (pow_nonneg ht (ri+rj))]

end DeficientGraph
end LocalLaw
