import SpectralConsequences.MomentIncrementPolynomial

/-! # A local reversible moment estimate

The conditional drift and exit integrals are separate quantities. The
symmetric increment is bounded here from actual pointwise increments.
-/
open scoped BigOperators
noncomputable section
namespace SpectralConsequences
open LocalLaw

theorem reversible_site_moment_bound {X:Type*}[Fintype X]
    (w:X→ℝ) (hw:∀x,0≤w x) (hmass:∑x,w x≤1) (E:ReversibleExtension X w)
    (Ω A:X→Prop) [DecidablePred Ω] [DecidablePred A] (hAΩ:∀x,A x→Ω x)
    (h target F:X→ℂ) (p:ℕ) (hp:1≤p)
    (B J ε V Rdrift Rexit:ℝ) (hε:0≤ε) (hV:0≤V)
    (hlocal:∀ω,A (E.project ω)→A (E.project (E.switching ω))→
      ‖h (E.project ω)-h (E.project (E.switching ω))‖≤ε)
    (hglobal:∀ω,A (E.project ω)→A (E.project (E.switching ω))→
      ‖F (E.project ω)-F (E.project (E.switching ω))‖≤V)
    (hdrift:‖finiteExpectation E.weight (fun ω=>if A (E.project ω) then
      (h (E.project (E.switching ω))-target (E.project ω))*complexMomentTest p (F (E.project ω)) else 0)‖≤
      B*(∑x,if Ω x then w x*‖F x‖^(2*p-1) else 0)+Rdrift)
    (hexit:‖finiteExpectation E.weight (fun ω=>if A (E.project ω) ∧ ¬A (E.project (E.switching ω)) then
      (h (E.project ω)-h (E.project (E.switching ω)))*complexMomentTest p (F (E.project ω)) else 0)‖≤
      J*(∑x,if Ω x then w x*‖F x‖^(2*p-1) else 0)+Rexit):
    ‖finiteExpectation w (fun x=>if A x then (h x-target x)*complexMomentTest p (F x) else 0)‖≤
      (B+J)*(∑x,if Ω x then w x*‖F x‖^(2*p-1) else 0)+
      momentIncrementCoefficient p*ε*V*(∑x,if Ω x then w x*‖F x‖^(2*p-2) else 0)+
      momentIncrementCoefficient p*ε*V^(2*p-1)+Rdrift+Rexit:=by
  classical
  let inc:=finiteExpectation E.weight (fun ω=>if A (E.project ω) ∧ A (E.project (E.switching ω)) then
    (h (E.project ω)-h (E.project (E.switching ω)))*
      (complexMomentTest p (F (E.project ω))-complexMomentTest p (F (E.project (E.switching ω)))) else 0)
  have hinc:=reversible_symmetric_moment_increment w E Ω A hAΩ h F p hp ε V hε hV hlocal hglobal
  have hΩmass:eventMass w Ω≤1:=by
    apply (Finset.sum_le_sum (fun x (_:x∈(Finset.univ:Finset X))=>?_)).trans hmass
    split_ifs
    · exact le_rfl
    · exact hw x
  have hconst:momentIncrementCoefficient p*ε*V*(V^(2*p-2)*eventMass w Ω)≤
      momentIncrementCoefficient p*ε*V^(2*p-1):=by
    have hK:0 ≤ momentIncrementCoefficient p*ε*V*V^(2*p-2):=by
      dsimp only [momentIncrementCoefficient];positivity
    have hh:=mul_le_of_le_one_right hK hΩmass
    have he:2*p-1=(2*p-2)+1:=by omega
    rw [he,pow_succ]
    convert hh using 1 <;>ring
  have hi:‖inc‖≤
      momentIncrementCoefficient p*ε*V*(∑x,if Ω x then w x*‖F x‖^(2*p-2) else 0)+
      momentIncrementCoefficient p*ε*V^(2*p-1):=by
    apply hinc.trans
    rw [mul_add]
    exact add_le_add_left hconst _
  have hhalf:‖(2:ℂ)⁻¹*inc‖≤‖inc‖:=by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (by norm_num)
  have hid:=reversible_site_test_identity w E A h target (fun x=>complexMomentTest p (F x))
  rw [hid]
  have ht:=(norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add hdrift (hhalf.trans hi))) hexit)
  apply ht.trans_eq
  ring

end SpectralConsequences
