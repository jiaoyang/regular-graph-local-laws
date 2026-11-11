import LocalLaw.UnionBallExcess
import LocalLaw.GraphSetBallExpansion

/-!
# Half-radius union excess under the source radius budget

Expanding the center set by one step removes the extra radius unit needed
by cross-edge counting. Thus the literal floor(R/2) union is bounded using
only radius-R excess, including even R, with a fixed degree/count constant.
-/

noncomputable section
namespace LocalLaw
local instance halfUnionExcessDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*} [Fintype V] [DecidableEq V]

def halfRadiusUnionExcessConstant (d m ω : ℕ) : ℕ :=
  (m * (d + 1)) * ω + (m * (d + 1)) ^ 2 * (ω + 1)

theorem graphSetBall_halfRadius_excess_bound (G : SimpleGraph V) (S : Set V) (d R ω : ℕ)
    (hR : 2 ≤ R) (hdegree : ∀ v, G.degree v ≤ d)
    (hbudget : ∀ v, graphBallExcess G v R ≤ ω) :
    graphExcess (G.induce (graphSetBall G S (R / 2))) ≤
      halfRadiusUnionExcessConstant d (Nat.card S) ω := by
  let S' := graphSetBall G S 1
  let r := R / 2 - 1
  have hr : r + 1 = R / 2 := by dsimp only [r]; omega
  have hsmall : 2 * r + 1 ≤ R := by dsimp only [r]; omega
  have hlocal : ∀ v, graphBallExcess G v (2 * r + 1) ≤ ω := fun v =>
    (graphBallExcess_mono_radius G v hsmall).trans (hbudget v)
  have hh := graphSetBall_excess_bound G S' r ω hlocal
  have heq : graphSetBall G S' r = graphSetBall G S (R / 2) := by
    dsimp only [S']
    rw [graphSetBall_expand_centers_one, hr]
  rw [heq] at hh
  have hcard : Nat.card S' ≤ Nat.card S * (d + 1) := by
    simpa only [S', pow_one] using graphSetBall_card_bound G S d hdegree 1
  apply hh.trans
  unfold halfRadiusUnionExcessConstant
  gcongr

end LocalLaw
