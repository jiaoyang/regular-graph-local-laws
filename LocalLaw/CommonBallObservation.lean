import LocalLaw.SingletonObservationLocalization
import LocalLaw.SingletonBallModel

/-!
# Singleton observations on the actual adjacent-endpoint common ball

The common finite model is the literal radius-(r+1) ball. Its reference class,
all intrinsic diameter caps, pair-model identities and post-deletion target
identity are derived. The error radius can be chosen independently of the
model radius used here.
-/

noncomputable section
set_option maxHeartbeats 1200000
namespace LocalLaw
local instance commonBallObservationDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace DeficientGraph
variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

theorem deleteVertex_H (g : DeficientGraph V d) (b : V) :
    (g.deleteVertex b).H = deletedMatrix g.H b :=
  normalizedAdjacency_induce g.graph d {v | v ≠ b}

theorem deleteVertex_G (g : DeficientGraph V d) (b : V) (z : ℂ) :
    (g.deleteVertex b).G z = green (deletedMatrix g.H b) z := by
  change green (g.deleteVertex b).H z = _
  rw [g.deleteVertex_H]

/-- The physical observation at an oriented edge is bounded using only
four genuine pair-model approximations, a local structural excess bound,
and the weak scalar prior. No final observation or Green bound is assumed. -/
theorem common_ball_singleton_observation (g : DeficientGraph V d) (hd : 3 ≤ d)
    (b c : V) (hbc : g.graph.Adj b c) (r : ℕ)
    (hzero : ∀ v ∈ graphBallVertices g.graph c (r + 1), g.deficit v = 0)
    (hbudget : graphBallExcess g.graph c (r + 1) ≤ finiteOmega d)
    (q z : ℂ) (hz : 0 < z.im) (hq : 0 ≤ q.im) (B : ℝ) (hB : ‖z‖ ≤ B)
    (ε L A δ : ℝ) (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hL : 1 ≤ L) (hA : 0 ≤ A)
    (hcap : ε * L ^ 4 ≤ 1)
    (hprior : ‖q - semicircleRoot z‖ ≤ scalarScale (spectralScale z) ε)
    (R : ℕ) (hRcap : (finiteOmega d + 1) * (4 * (r + 1) + 1) ≤ R)
    (hRlog : (R : ℝ) + 1 ≤ A * L) (hrlog : ((4 * r + 1 : ℕ) + 1 : ℝ) ≤ A * L)
    (hlarge : localizationBudgetConstant d B A ≤ L)
    (htail : physicalTransfer d z ^ (2 * r) ≤ ε)
    (hcc : ‖g.G z c c - g.P r z q c c‖ ≤ δ)
    (hcb : ‖g.G z c b - g.P r z q c b‖ ≤ δ)
    (hbc' : ‖g.G z b c - g.P r z q b c‖ ≤ δ)
    (hbb : ‖g.G z b b - g.P r z q b b‖ ≤ δ)
    (smallPivot : singletonPivotBudget d q z (2 * finiteExtraReferenceConstant d) *
      (δ + localizationWeakConstant d B A * L * ε) ≤ 1 / 2) :
    ‖(g.deleteVertex b).G z ⟨c, hbc.ne.symm⟩ ⟨c, hbc.ne.symm⟩ -
      (g.deleteVertex b).P r z q ⟨c, hbc.ne.symm⟩ ⟨c, hbc.ne.symm⟩‖ ≤
        singletonObservationBudget d B A L ε δ := by
  let S := graphBallVertices g.graph c (r + 1)
  let M := g.restrict S
  let cc : S := ⟨c, center_mem_graphBall g.graph c (r + 1)⟩
  have hb : b ∈ S := (adjacent_ball_subset_succ g.graph hbc r) (center_mem_graphBall g.graph b r)
  let bb : S := ⟨b, hb⟩
  let ii : {v : S // v ≠ bb} := ⟨cc, fun hh => hbc.ne (congrArg Subtype.val hh).symm⟩
  have hconn : M.graph.Connected := graphBall_connected g.graph c (r + 1)
  have hzeroM : ∀ v, M.deficit v = 0 := fun v => hzero v.val v.property
  have hbudgetM : M.ComponentReferenceBudget :=
    M.connected_zero_component_budget hconn hzeroM hbudget
  have hdiam : ∀ k l, M.graph.dist k l ≤ 2 * (r + 1) :=
    graphBall_distance_le_twice_radius g.graph c (r + 1)
  have hRfull : ∀ k l, M.graph.dist k l ≤ R := by
    intro k l
    apply (hdiam k l).trans
    apply le_trans _ hRcap
    nlinarith [Nat.zero_le (finiteOmega d)]
  have hRdel : ∀ k l, (M.deleteVertex bb).graph.dist k l ≤ R := by
    intro k l
    exact (M.deleteVertex_distance_bound hconn hbudget bb (2 * (r + 1)) hdiam k l).trans
      (by convert hRcap using 1; ring)
  have hballc : graphBallVertices g.graph c r ⊆ S :=
    graphBallVertices_mono g.graph c (by omega)
  have hballb : graphBallVertices g.graph b r ⊆ S := adjacent_ball_subset_succ g.graph hbc r
  have hpcc : M.P r z q cc cc = g.P r z q c c := g.restrict_pair_P S cc cc r hballc hballc q z
  have hpcb : M.P r z q cc bb = g.P r z q c b := g.restrict_pair_P S cc bb r hballc hballb q z
  have hpbc : M.P r z q bb cc = g.P r z q b c := g.restrict_pair_P S bb cc r hballb hballc q z
  have hpbb : M.P r z q bb bb = g.P r z q b b := g.restrict_pair_P S bb bb r hballb hballb q z
  let e : S ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  have hh := M.embedded_singleton_pair_observation hd hzeroM hbudgetM g.H
    (normalizedAdjacency_isHermitian g.graph d) e q z hz hq B hB ε L A δ hε hδ hL hA hcap
    hprior R r bb ii hRfull hRdel hRlog hrlog hlarge htail
      (by change ‖g.G z c c - M.P r z q cc cc‖ ≤ δ; rw [hpcc]; exact hcc)
      (by change ‖g.G z c b - M.P r z q cc bb‖ ≤ δ; rw [hpcb]; exact hcb)
      (by change ‖g.G z b c - M.P r z q bb cc‖ ≤ δ; rw [hpbc]; exact hbc')
      (by change ‖g.G z b b - M.P r z q bb bb‖ ≤ δ; rw [hpbb]; exact hbb) smallPivot
  have hpdel := g.restrict_deleteVertex_pair_P S bb ii r hballc q z
  rw [hpdel, ← g.deleteVertex_G] at hh
  exact hh

end DeficientGraph
end LocalLaw
