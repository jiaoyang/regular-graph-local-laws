import LocalLaw.SourceCommonLeafKernelDecay
import LocalLaw.SampledFarKernel
import LocalLaw.DeficientGraphInstanceTransport

/-! # Explicit equality-instance transport for common-core decay -/
open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance leafCoreFarAdapterDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace DeficientGraph
variable {V:Type} [Fintype V] [DecidableEq V] {d:ℕ}

theorem sampled_far_column_of_leafCoreDecayBound (g:DeficientGraph V d)(hd:3≤d)(T:Set V)
    (q z:ℂ)(hz:0<z.im)(hq:0≤q.im)(K L ε Kdiag δ a:ℝ)
    (hK:0≤K)(hL:0≤L)(hε:0≤ε)(hKdiag:0≤Kdiag)(hδ:0≤δ)
    (hcore:g.LeafCoreDecayBound T q z K L ε)
    (x:(Tᶜ:Set V))(b:T)(h:ℕ)(hfar:((h+1:ℕ):ℕ∞)≤g.graph.edist x.val b.val)
    (hdiag:‖g.extensionGreen q z b.val b.val‖≤Kdiag)
    (hoff:∀j:T,j≠b→‖g.extensionGreen q z j.val b.val‖≤δ)
    (hrows:letI : DecidableEq (Tᶜ:Set V):=fun a b=>Classical.propDecidable (a=b)
      (∑j:T,‖((g.delete T).extensionGreen q z*g.H.submatrix
      (Subtype.val:(Tᶜ:Set V)→V) (Subtype.val:T→V)) x j‖)≤a) :
    ‖g.extensionGreen q z x.val b.val‖≤
      Kdiag*((K*L*physicalTransfer d z^h+K*L*ε)*((d:ℝ)/Real.sqrt ((d:ℝ)-1)))+δ*a := by
  have hc:∀u v:(Tᶜ:Set V),∀n:ℕ,(n:ℕ∞)≤(g.delete T).graph.edist u v→
      ‖(g.delete T).extensionGreen q z u v‖≤K*L*physicalTransfer d z^n+K*L*ε := by
    intro u v n hn
    dsimp only [LeafCoreDecayBound] at hcore
    have hh:=hcore u v n hn
    have he:=extensionGreen_decidableEq_eq (g.delete T)
      (fun a b=>Classical.propDecidable (a=b)) inferInstance q z
    rw [he] at hh
    exact hh
  have hr:(∑j:T,‖((g.delete T).extensionGreen q z*g.H.submatrix
      (Subtype.val:(Tᶜ:Set V)→V) (Subtype.val:T→V)) x j‖)≤a := by
    have he:=extensionGreen_decidableEq_eq (g.delete T)
      (fun a b=>Classical.propDecidable (a=b)) inferInstance q z
    rw [he] at hrows
    exact hrows
  exact g.sampled_far_column_from_core hd T q z hz hq K L ε Kdiag δ a
    hK hL hε hKdiag hδ hc x b h hfar hdiag hoff hr

end DeficientGraph
end LocalLaw
