import LocalLaw.LeafPaddedLocalization
import LocalLaw.EndpointRootOccupancy

/-! # Uniform target rows on mutually separated leaves

A radius-r ball around an arbitrary target contains at most one leaf.
This controls rows from original core targets as well as leaf targets.
-/

open scoped BigOperators
noncomputable section
namespace LocalLaw
local instance separatedTargetLeafDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V I : Type} [Fintype V] [Fintype I]

theorem separated_index_ball_card_le_one (G : SimpleGraph V) (e : I→V) (r : ℕ)
    (hsep : ∀ a b,a≠b→(2*r:ℕ∞)<G.edist (e a) (e b)) (x : V) :
    Nat.card {l:I | G.edist x (e l)≤(r:ℕ∞)}≤1 := by
  apply (Finite.card_le_one_iff_subsingleton).mpr
  constructor
  intro a b
  apply Subtype.ext
  by_contra hab
  have hf:=hsep a.val b.val hab
  have hh:G.edist (e a.val) (e b.val)≤(2*r:ℕ∞):=by
    calc
      _≤G.edist (e a.val) x+G.edist x (e b.val):=G.edist_triangle
      _≤(r:ℕ∞)+(r:ℕ∞):=add_le_add
        (by simpa only [SimpleGraph.edist_comm] using a.property) b.property
      _=(2*r:ℕ∞):=by norm_cast;omega
  exact not_lt_of_ge hh hf

namespace DeficientGraph
variable [DecidableEq V] {d : ℕ}

theorem separated_target_leaf_rows (g : DeficientGraph V d) (hd : 3≤d)
    (hb : g.ComponentFiniteReferenceBudget) (e : I→V) (r : ℕ)
    (hsep : ∀ a b,a≠b→(2*r:ℕ∞)<g.graph.edist (e a) (e b))
    (q z : ℂ) (hz : 0<z.im) (hq : 0≤q.im) (R : ℕ) (hR : ∀ x y,g.graph.dist x y≤R)
    (small : ‖q-semicircleRoot z‖*finiteExtraReferenceConstant d*
      coreConvolutionConstant (finiteOmega d+1)*((R:ℝ)+1)≤1/2)
    (hcount : (Fintype.card I:ℝ)*physicalTransfer d z^r≤1) :
    (∀x, (∑l:I,‖g.extensionGreen q z x (e l)‖)≤4*finiteExtraReferenceConstant d) ∧
      (∀x, (∑l:I,‖g.extensionGreen q z (e l) x‖)≤4*finiteExtraReferenceConstant d) := by
  have hC:0≤2*finiteExtraReferenceConstant d:=by linarith [finiteExtraReferenceConstant_ge_one d hd]
  have ht:0≤physicalTransfer d z:=(physicalTransfer_pos d hd z).le
  have ht1:physicalTransfer d z≤1:=by nlinarith [physicalTransfer_sq_le_half d hd z]
  have hk:=g.componentwise_finite_kernel_decay hd hb q z hz hq R hR small
  have hrow (x:V):(∑l:I,‖g.extensionGreen q z x (e l)‖)≤4*finiteExtraReferenceConstant d:=by
    let near:=fun l:I=>g.graph.edist x (e l)≤(r:ℕ∞)
    have hn:(Nat.card {l:I | near l}:ℝ)≤1:=by
      exact_mod_cast separated_index_ball_card_le_one g.graph e r hsep x
    have hcap (l:I):‖g.extensionGreen q z x (e l)‖≤2*finiteExtraReferenceConstant d:=
      (hk x (e l)).trans (mul_le_of_le_one_right hC (pow_le_one₀ ht ht1))
    have hfar (l:I) (hl:¬near l):
        ‖g.extensionGreen q z x (e l)‖≤2*finiteExtraReferenceConstant d*physicalTransfer d z^r:=
      g.perturbed_green_edist_bound hd hb z q hz hq R hR small x (e l) r (lt_of_not_ge hl).le
    have hh:=finite_kernel_near_far_sum (fun l=>g.extensionGreen q z x (e l)) near 1
      (2*finiteExtraReferenceConstant d) (physicalTransfer d z^r) hC (pow_nonneg ht r) hn hcap hfar
    have hc:=mul_le_mul_of_nonneg_left hcount hC
    nlinarith only [hh,hc]
  refine ⟨hrow,fun x=>?_⟩
  simpa only [(g.extensionGreen_isSymm q z).apply] using hrow x

end DeficientGraph
end LocalLaw
