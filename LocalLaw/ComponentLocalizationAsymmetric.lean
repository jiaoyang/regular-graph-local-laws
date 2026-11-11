import LocalLaw.ConnectedLocalizationAsymmetric
import LocalLaw.ComponentFiniteLocalization

/-! # Componentwise asymmetric localization into arbitrary retained sets -/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2200000
namespace LocalLaw
local instance componentLocalizationAsymmetricDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance (priority := high) componentLocalizationAsymMemDecidable
    {A : Type*} (H : SimpleGraph A) (C : H.ConnectedComponent) :
    DecidablePred (fun a=>a∈C.supp) := fun _=>Classical.propDecidable _
namespace DeficientGraph
variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

theorem asymmetricLocalizationBound_nonnegative (d : ℕ) (hd : 3≤d) (q z : ℂ) (B : ℝ) (R ri rj : ℕ) :
    0≤asymmetricLocalizationBound d q z B R ri rj := by
  have hC : 0≤finiteExtraReferenceConstant d := (by norm_num : (0:ℝ)≤1).trans (finiteExtraReferenceConstant_ge_one d hd)
  have hC0:=coreConvolutionConstant_nonnegative (finiteOmega d+1)
  have hτ:=ordinaryFeedbackBudget_nonnegative z q B R
  have hD : 0<(d:ℝ)-1 := by have hh : (3:ℝ)≤d := Nat.cast_le.mpr hd; linarith
  have hmass : 0≤localizationExceptionalMass d q := by
    unfold localizationExceptionalMass
    exact div_nonneg (by positivity) hD.le
  have hratio : 0≤((finiteOmega d:ℝ)+1)/((d:ℝ)-1) := div_nonneg (by positivity) hD.le
  have ht : 0≤physicalTransfer d z := norm_nonneg _
  unfold asymmetricLocalizationBound
  positivity

theorem componentwise_restriction_localization_asymmetric (g : DeficientGraph V d) (hd : 3≤d)
    (hbudget : g.ComponentFiniteReferenceBudget) (S : Set V)
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
  let C:=g.graph.connectedComponentMk i.val
  let M:=g.restrict S
  let U : Set S:={v | v.val∈C.supp}
  have hi : i.val∈C.supp := rfl
  have hcutU : ∀ a∈U,∀ b∉U,¬M.graph.Adj a b := by
    intro a ha b hb hab
    exact g.component_cut C a.val ha b.val hb hab
  by_cases hj : j.val∈C.supp
  · let gC:=g.restrict C.supp
    let SC : Set C.supp:={v | v.val∈S}
    let ii : SC:=⟨⟨i.val,hi⟩,i.property⟩
    let jj : SC:=⟨⟨j.val,hj⟩,j.property⟩
    let e : (M.graph.induce U)≃g(gC.graph.induce SC) :=
      { toEquiv:=
          { toFun:=fun v=>⟨⟨v.val.val,v.property⟩,v.val.property⟩
            invFun:=fun v=>⟨⟨v.val.val,v.property⟩,v.val.property⟩
            left_inv:=fun _=>rfl
            right_inv:=fun _=>rfl }
        map_rel_iff':=Iff.rfl }
    have hCR (a b : C.supp) : gC.graph.dist a b≤R := by
      change (g.graph.induce C.supp).dist a b≤R
      rw [isolated_induce_distance g.graph C.supp (g.component_cut C)]
      exact hR a.val b.val
    have hSCR (a b : SC) : (gC.restrict SC).graph.dist a b≤Rs := by
      have he:=graphIso_dist e (e.symm a) (e.symm b)
      have hh : (M.graph.induce U).dist (e.symm a) (e.symm b)≤Rs := by
        rw [isolated_induce_distance M.graph U hcutU]
        exact hRs (e.symm a).val (e.symm b).val
      simpa only [e.apply_symm_apply] using he.trans_le hh
    have hCI : graphBallVertices gC.graph ii.val ri⊆SC := by
      intro a ha
      exact hI ((isolated_graphBall_mem g.graph C.supp (g.component_cut C) ii.val ri a).mp ha)
    have hCJ : graphBallVertices gC.graph jj.val rj⊆SC := by
      intro a ha
      exact hJ ((isolated_graphBall_mem g.graph C.supp (g.component_cut C) jj.val rj a).mp ha)
    have hh:=gC.connected_restriction_localization_asymmetric hd C.connected_induce_supp (hbudget C) SC
      q z hz hq B hzB R Rs hCR hSCR smallG smallS smallOutside smallCavity smallOrdinary ii jj ri rj hCI hCJ
    have hFull:=g.restrict_extensionGreen_of_isolated hd C.supp (g.component_cut C) q z hz hq
    have hLocal:=M.restrict_extensionGreen_of_isolated hd U hcutU q z hz hq
    have hIso:=(gC.restrict SC).extensionGreen_iso (M.restrict U) e (fun _=>rfl) q z
    have hfull : gC.extensionGreen q z ii.val jj.val=g.extensionGreen q z i.val j.val :=
      congrArg (fun A : Matrix C.supp C.supp ℂ=>A ii.val jj.val) hFull
    have hlocal : (gC.restrict SC).extensionGreen q z ii jj=M.extensionGreen q z i j :=
      (congrArg (fun A : Matrix U U ℂ=>A ⟨i,hi⟩ ⟨j,hj⟩) hIso).trans
        (congrArg (fun A : Matrix U U ℂ=>A ⟨i,hi⟩ ⟨j,hj⟩) hLocal)
    rw [hfull,hlocal] at hh
    exact hh
  · have hzeroFull:=g.extensionGreen_zero_across_cut hd C.supp (g.component_cut C) q z hz hq i.val hi j.val hj
    have hzeroLocal:=M.extensionGreen_zero_across_cut hd U hcutU q z hz hq i hi j hj
    rw [hzeroFull,hzeroLocal,sub_zero,norm_zero]
    exact asymmetricLocalizationBound_nonnegative d hd q z B R ri rj

end DeficientGraph
end LocalLaw
