import LocalLaw.DeletedSampleCrossBound
import LocalLaw.DeletedCouplingFarBound

/-! # Far sampled columns from the actual common-core kernel decay -/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance sampledFarKernelDecidable (p:Prop):Decidable p:=Classical.propDecidable p
namespace DeficientGraph
variable {V:Type} [Fintype V] [DecidableEq V] {d:ℕ}

theorem sampled_far_column_from_core (g:DeficientGraph V d)(hd:3≤d)(T:Set V)
    (q z:ℂ)(hz:0<z.im)(hq:0≤q.im)(K L ε Kdiag δ a:ℝ)
    (hK:0≤K)(hL:0≤L)(hε:0≤ε)(hKdiag:0≤Kdiag)(hδ:0≤δ)
    (hcore:∀x y:(Tᶜ:Set V),∀h:ℕ,(h:ℕ∞)≤(g.delete T).graph.edist x y→
      ‖(g.delete T).extensionGreen q z x y‖≤K*L*physicalTransfer d z^h+K*L*ε)
    (x:(Tᶜ:Set V))(b:T)(h:ℕ)(hfar:((h+1:ℕ):ℕ∞)≤g.graph.edist x.val b.val)
    (hdiag:‖g.extensionGreen q z b.val b.val‖≤Kdiag)
    (hoff:∀j:T,j≠b→‖g.extensionGreen q z j.val b.val‖≤δ)
    (hrows:(∑j:T,‖((g.delete T).extensionGreen q z*g.H.submatrix
      (Subtype.val:(Tᶜ:Set V)→V) (Subtype.val:T→V)) x j‖)≤a) :
    ‖g.extensionGreen q z x.val b.val‖≤
      Kdiag*((K*L*physicalTransfer d z^h+K*L*ε)*((d:ℝ)/Real.sqrt ((d:ℝ)-1)))+δ*a := by
  let F:=K*L*physicalTransfer d z^h+K*L*ε
  have hF:0≤F:=by
    have ht:0≤physicalTransfer d z^h:=pow_nonneg (physicalTransfer_pos d hd z).le _
    dsimp only [F]
    positivity
  have hb:b.val∉pairBallVertices g.graph x.val x.val h:=by
    intro hb
    have hh:g.graph.edist x.val b.val≤(h:ℕ∞):=hb.elim id id
    have hbad:((h+1:ℕ):ℕ∞)≤(h:ℕ∞):=hfar.trans hh
    have hh':h+1≤h:=ENat.coe_le_coe.mp hbad
    omega
  have hnear:∀v:(Tᶜ:Set V),g.graph.Adj v.val b.val→
      ‖(g.delete T).extensionGreen q z x v‖≤F:=by
    intro v hv
    have hh:=(omitted_pair_neighbor_far g.graph x.val x.val b.val v.val h hb hv).1
    exact hcore x v h (hh.trans (graphHom_edist_le (SimpleGraph.Embedding.induce (G:=g.graph) Tᶜ).toHom x v))
  have hc:=g.cut_coupling_far_column_bound T ((g.delete T).extensionGreen q z) x b F hF hnear
  have hf:0≤F*((d:ℝ)/Real.sqrt ((d:ℝ)-1)):=by positivity
  exact g.deleted_sample_cross_bound hd T q z hz hq x b Kdiag δ
    (F*((d:ℝ)/Real.sqrt ((d:ℝ)-1))) a hKdiag hδ hf hdiag hoff hc hrows

end DeficientGraph
end LocalLaw
