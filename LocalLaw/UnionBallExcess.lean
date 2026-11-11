import LocalLaw.NearestCenterForest
import LocalLaw.GeneralPartitionExcess

/-!
# Actual excess of a union of finitely many balls

Nearest-center parent cells form a genuine connected partition, even when the
union itself is disconnected. Each cell inherits the ambient ball budget and
each pair has at most omega+1 cross edges. The resulting polynomial bound
depends only on the number of supplied centers and the local excess budget.
-/

noncomputable section
set_option maxHeartbeats 1800000
namespace LocalLaw
local instance unionBallExcessDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V : Type*} [Fintype V]

theorem induced_graphBallExcess_le (G : SimpleGraph V) (S : Set V) (o : S) (r : ℕ) :
    graphBallExcess (G.induce S) o r ≤ graphBallExcess G o.val r := by
  let f : graphBall (G.induce S) o r →g graphBall G o.val r :=
    { toFun := fun v => ⟨v.val.val,
        (graphHom_edist_le (SimpleGraph.Embedding.induce S).toHom o v.val).trans v.property⟩
      map_rel' := fun h => h }
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : graphBallVertices G o.val r => z.val) h
  exact connected_embedding_graphExcess_le _ _ (graphBall_connected _ _ _) (graphBall_connected _ _ _) f hf

theorem connected_radius_cell_excess_bound (G : SimpleGraph V) (S : Set V)
    (hS : (G.induce S).Connected) (o : V) (r R ω : ℕ) (hr : r ≤ R)
    (hradius : ∀ x ∈ S, G.edist o x ≤ (r : ℕ∞))
    (hbudget : graphBallExcess G o R ≤ ω) : graphExcess (G.induce S) ≤ ω := by
  let f : G.induce S →g graphBall G o R :=
    { toFun := fun x => ⟨x.val, (hradius x.val x.property).trans (ENat.coe_le_coe.mpr hr)⟩
      map_rel' := fun h => h }
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : graphBallVertices G o R => z.val) h)
  exact (connected_embedding_graphExcess_le _ _ hS (graphBall_connected _ _ _) f hf).trans hbudget

/-- A finite union of radius-r balls has a polynomial excess budget. All
connected cells, root counts and cross-edge multiplicities are derived. -/
theorem radius_partition_excess_bound {I : Type*} [Fintype I]
    (G : SimpleGraph V) (f : V → I) (center : I → V) (r ω : ℕ)
    (hcell : ∀ i, (G.induce {v | f v = i}).Connected)
    (hradius : ∀ i v, f v = i → G.edist (center i) v ≤ (r : ℕ∞))
    (hlocal : ∀ v, graphBallExcess G v (2 * r + 1) ≤ ω) :
    graphExcess G ≤ Nat.card I * ω + (Nat.card I) ^ 2 * (ω + 1) := by
  have hcellbudget : ∀ i, graphExcess (G.induce {v | f v = i}) ≤ ω := by
    intro i
    exact connected_radius_cell_excess_bound G _ (hcell i) (center i) r (2 * r + 1) ω (by omega)
      (hradius i) (hlocal (center i))
  have hcross : ∀ i j, i ≠ j →
      Nat.card (CellCrossEdge G {v | f v = i} {v | f v = j}) ≤ ω + 1 := by
    intro i j hij
    have hdisj : Disjoint {v : V | f v = i} {v : V | f v = j} :=
      Set.disjoint_left.mpr (fun _ hi hj => hij (hi.symm.trans hj))
    exact connected_cell_cross_edge_bound G _ _ hdisj (hcell i) (hcell j) (center i) (center j) r ω
      (hradius i) (hradius j) hlocal
  exact partition_excess_bound G f hcell ω (ω + 1) hcellbudget hcross

theorem graphSetBall_excess_bound (G : SimpleGraph V) (S : Set V) (r ω : ℕ)
    (hbudget : ∀ v, graphBallExcess G v (2 * r + 1) ≤ ω) :
    graphExcess (G.induce (graphSetBall G S r)) ≤
      Nat.card S * ω + (Nat.card S) ^ 2 * (ω + 1) := by
  let U := graphSetBall G S r
  let H := G.induce U
  let D := setBallHeightForest G S r
  let I := {v : U // D.height v = 0}
  have hparent := setBallHeightForest_parent_adj G S r
  have hheight : ∀ v : U, D.height v ≤ r := setBallHeight_le G S r
  have hlocal : ∀ v : U, graphBallExcess H v (2 * r + 1) ≤ ω := fun v =>
    (induced_graphBallExcess_le G U v _).trans (hbudget v.val)
  have hcell : ∀ i : I, (H.induce {v | D.rootLabel v = i}).Connected := D.cell_connected H hparent
  have hradius : ∀ (i : I) (v : U), D.rootLabel v = i → H.edist i.val v ≤ (r : ℕ∞) :=
    D.cell_radius H hparent r hheight
  have hh := radius_partition_excess_bound H D.rootLabel (fun i : I => i.val) r ω hcell hradius hlocal
  have hm : Nat.card I = Nat.card S := Nat.card_congr (setBallZeroRootEquiv G S r)
  change graphExcess H ≤ Nat.card I * ω + (Nat.card I) ^ 2 * (ω + 1) at hh
  rw [hm] at hh
  exact hh

end LocalLaw
