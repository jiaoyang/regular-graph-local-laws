import SpectralConsequences.GlobalReversibleMomentBound

/-! Zero-weight enlarged states may contain an arbitrary auxiliary set.
Make their switch the identity; every actual weighted integral is unchanged.
The moment recurrence consequently needs increments only on nonzero support. -/
open scoped BigOperators
noncomputable section
namespace LocalLaw
open SpectralConsequences
local instance supportedReversibleMomentDecidable (p:Prop):Decidable p:=Classical.propDecidable p

namespace ReversibleExtension
variable {X:Type*} [Fintype X] {w:X→ℝ}

def supportSwitch (E:LocalLaw.ReversibleExtension X w) (ω:E.space):E.space:=
  if E.weight ω=0 then ω else E.switching ω

theorem supportSwitch_involutive (E:LocalLaw.ReversibleExtension X w):
    Function.Involutive E.supportSwitch:=by
  intro ω
  by_cases h:E.weight ω=0
  · simp only [supportSwitch,h,if_true]
  · have hs:E.weight (E.switching ω)≠0:=by rw [E.preserve];exact h
    simp only [supportSwitch,h,if_false,hs]
    exact E.involution ω

def onSupport (E:LocalLaw.ReversibleExtension X w):LocalLaw.ReversibleExtension X w where
  space:=E.space
  finite:=E.finite
  weight:=E.weight
  nonnegative:=E.nonnegative
  project:=E.project
  marginal:=E.marginal
  switching:=Function.Involutive.toPerm E.supportSwitch E.supportSwitch_involutive
  preserve:=by
    intro ω
    change E.weight (supportSwitch E ω)=E.weight ω
    unfold supportSwitch
    split_ifs
    · rfl
    · exact E.preserve ω
  involution:=E.supportSwitch_involutive

@[simp] theorem onSupport_switch (E:LocalLaw.ReversibleExtension X w)(ω:E.space):
    E.onSupport.switching ω=if E.weight ω=0 then ω else E.switching ω:=rfl

theorem onSupport_expectation (E:LocalLaw.ReversibleExtension X w)
    (f:E.space→E.space→ℂ):
    finiteExpectation E.onSupport.weight (fun ω=>f ω (E.onSupport.switching ω))=
      finiteExpectation E.weight (fun ω=>f ω (E.switching ω)):=by
  unfold finiteExpectation
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h:E.weight ω=0
  · simp only [onSupport,h,Complex.ofReal_zero,zero_mul]
  · simp only [onSupport_switch,h,if_false]
    rfl

end ReversibleExtension
end LocalLaw

namespace SpectralConsequences
open LocalLaw
/-- The genuine recurrence with hypotheses only on weighted support. -/
theorem global_reversible_moment_recurrence_on_support {X I:Type*} [Fintype X] [Fintype I] [Nonempty I]
    (w:X→ℝ) (hw:∀x,0≤w x) (hmass:∑x,w x≤1)
    (E:I→LocalLaw.ReversibleExtension X w) (Ω:X→Prop) [DecidablePred Ω]
    (χ:I→X→Prop) [∀i,DecidablePred (χ i)]
    (h:I→X→ℂ) (target F error:X→ℂ) (p:ℕ) (hp:1≤p)
    (B J Sparse ε V Rdrift Rexit:ℝ) (hε:0≤ε) (hV:0≤V)
    (hmean:∀x,Ω x→F x=finiteComplexMean (fun i=>if χ i x then h i x-target x else 0)+error x)
    (hsparse:∀x,Ω x→‖error x‖≤Sparse)
    (hlocal:∀i ω,(E i).weight ω≠0→Ω ((E i).project ω)∧χ i ((E i).project ω)→
      Ω ((E i).project ((E i).switching ω))∧χ i ((E i).project ((E i).switching ω))→
      ‖h i ((E i).project ω)-h i ((E i).project ((E i).switching ω))‖≤ε)
    (hglobal:∀i ω,(E i).weight ω≠0→Ω ((E i).project ω)∧χ i ((E i).project ω)→
      Ω ((E i).project ((E i).switching ω))∧χ i ((E i).project ((E i).switching ω))→
      ‖F ((E i).project ω)-F ((E i).project ((E i).switching ω))‖≤V)
    (hdrift:∀i,‖finiteExpectation (E i).weight (fun ω=>
      if Ω ((E i).project ω)∧χ i ((E i).project ω) then
        (h i ((E i).project ((E i).switching ω))-target ((E i).project ω))*
          complexMomentTest p (F ((E i).project ω)) else 0)‖≤
      B*(∑x,if Ω x then w x*‖F x‖^(2*p-1) else 0)+Rdrift)
    (hexit:∀i,‖finiteExpectation (E i).weight (fun ω=>
      if (Ω ((E i).project ω)∧χ i ((E i).project ω)) ∧
          ¬(Ω ((E i).project ((E i).switching ω))∧χ i ((E i).project ((E i).switching ω))) then
        (h i ((E i).project ω)-h i ((E i).project ((E i).switching ω)))*
          complexMomentTest p (F ((E i).project ω)) else 0)‖≤
      J*(∑x,if Ω x then w x*‖F x‖^(2*p-1) else 0)+Rexit):
    truncatedMoment w Ω F p≤
      (B+J+Sparse)*(∑x,if Ω x then w x*‖F x‖^(2*p-1) else 0)+
      momentIncrementCoefficient p*ε*V*(∑x,if Ω x then w x*‖F x‖^(2*p-2) else 0)+
      momentIncrementCoefficient p*ε*V^(2*p-1)+Rdrift+Rexit:=by
  classical
  apply global_reversible_moment_recurrence w hw hmass (fun i=>(E i).onSupport) Ω χ h target F error
    p hp B J Sparse ε V Rdrift Rexit hε hV hmean hsparse
  · intro i ω hold hnew
    by_cases hzero:(E i).weight ω=0
    · simpa only [ReversibleExtension.onSupport_switch,hzero,if_true,sub_self,norm_zero] using hε
    · have he:(E i).onSupport.switching ω=(E i).switching ω:=by simp only [ReversibleExtension.onSupport_switch,hzero,if_false]
      rw [he] at hnew ⊢
      exact hlocal i ω hzero hold hnew
  · intro i ω hold hnew
    by_cases hzero:(E i).weight ω=0
    · simpa only [ReversibleExtension.onSupport_switch,hzero,if_true,sub_self,norm_zero] using hV
    · have he:(E i).onSupport.switching ω=(E i).switching ω:=by simp only [ReversibleExtension.onSupport_switch,hzero,if_false]
      rw [he] at hnew ⊢
      exact hglobal i ω hzero hold hnew
  · intro i
    have he:=(E i).onSupport_expectation (fun ω ξ=>
      if Ω ((E i).project ω)∧χ i ((E i).project ω) then
        (h i ((E i).project ξ)-target ((E i).project ω))*complexMomentTest p (F ((E i).project ω)) else 0)
    have hh:=hdrift i
    rw [←he] at hh
    exact hh
  · intro i
    have he:=(E i).onSupport_expectation (fun ω ξ=>
      if (Ω ((E i).project ω)∧χ i ((E i).project ω))∧¬(Ω ((E i).project ξ)∧χ i ((E i).project ξ)) then
        (h i ((E i).project ω)-h i ((E i).project ξ))*complexMomentTest p (F ((E i).project ω)) else 0)
    have hh:=hexit i
    rw [←he] at hh
    exact hh

end SpectralConsequences
