import SpectralConsequences.GlobalSiteMomentEnergy
import SpectralConsequences.ReversibleSiteMomentBound
import SpectralConsequences.ThreeTermMomentBootstrap

/-! # The finite fluctuation-averaging moment recurrence

Each site owns its actual reversible extension. Conditional drift, pointwise
increments, exit integrals, and the sparse-site averaging identity are
distinct inputs; the symmetric high-moment contribution is proved here.
-/
open scoped BigOperators
noncomputable section
namespace SpectralConsequences
open LocalLaw

theorem global_reversible_moment_recurrence {X I:Type*} [Fintype X] [Fintype I] [Nonempty I]
    (w:X→ℝ) (hw:∀x,0≤w x) (hmass:∑x,w x≤1)
    (E:I→ReversibleExtension X w) (Ω:X→Prop) [DecidablePred Ω]
    (χ:I→X→Prop) [∀i,DecidablePred (χ i)]
    (h:I→X→ℂ) (target F error:X→ℂ) (p:ℕ) (hp:1≤p)
    (B J Sparse ε V Rdrift Rexit:ℝ) (hε:0≤ε) (hV:0≤V)
    (hmean:∀x,Ω x→F x=finiteComplexMean (fun i=>if χ i x then h i x-target x else 0)+error x)
    (hsparse:∀x,Ω x→‖error x‖≤Sparse)
    (hlocal:∀i ω,Ω ((E i).project ω)∧χ i ((E i).project ω)→
      Ω ((E i).project ((E i).switching ω))∧χ i ((E i).project ((E i).switching ω))→
      ‖h i ((E i).project ω)-h i ((E i).project ((E i).switching ω))‖≤ε)
    (hglobal:∀i ω,Ω ((E i).project ω)∧χ i ((E i).project ω)→
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
  let M:=truncatedMoment w Ω F p
  have hM:0≤M:=by
    unfold M truncatedMoment
    exact Finset.sum_nonneg (fun x _=>by split_ifs;exact mul_nonneg (hw x) (by positivity);rfl)
  have hsite (i:I):‖finiteExpectation w (fun x=>if Ω x∧χ i x then
      (h i x-target x)*complexMomentTest p (F x) else 0)‖≤
      (B+J)*(∑x,if Ω x then w x*‖F x‖^(2*p-1) else 0)+
      momentIncrementCoefficient p*ε*V*(∑x,if Ω x then w x*‖F x‖^(2*p-2) else 0)+
      momentIncrementCoefficient p*ε*V^(2*p-1)+Rdrift+Rexit:=
    reversible_site_moment_bound w hw hmass (E i) Ω (fun x=>Ω x∧χ i x) (fun _ hx=>hx.1)
      (h i) target F p hp B J ε V Rdrift Rexit hε hV (hlocal i) (hglobal i) (hdrift i) (hexit i)
  have he:=truncated_moment_site_energy w Ω χ h target F error p hp hmean
  have herror:=truncated_moment_error_term w hw Ω F error p Sparse hsparse
  have hmeanNorm:=finiteComplexMean_norm_bound _ _ hsite
  have henergy: M≤
      ((B+J)*(∑x,if Ω x then w x*‖F x‖^(2*p-1) else 0)+
      momentIncrementCoefficient p*ε*V*(∑x,if Ω x then w x*‖F x‖^(2*p-2) else 0)+
      momentIncrementCoefficient p*ε*V^(2*p-1)+Rdrift+Rexit)+
      Sparse*(∑x,if Ω x then w x*‖F x‖^(2*p-1) else 0):=by
    have hn:=congrArg norm he
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hM] at hn
    rw [hn]
    exact (norm_add_le _ _).trans (add_le_add hmeanNorm herror)
  apply henergy.trans_eq
  ring

end SpectralConsequences
