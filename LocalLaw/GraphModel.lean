import LocalLaw.FiniteModel
import LocalLaw.FiniteResampling
import LocalLaw.Resolvent
import LocalLaw.RegularTree
import LocalLaw.Semicircle

/-!
# The actual finite regular-graph model

These definitions fix the original ensemble and physical Green functions,
minor average, finite graph balls, and pair-neighborhood extension model.
They do not assert the switching/concentration estimates in Sections 5 and 6.
The uniform law is normalized only under explicit nonemptiness of the ensemble.
-/

open scoped BigOperators

noncomputable section

namespace LocalLaw

local instance graphModelDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- All simple d-regular graphs with the actual vertex set Fin N. -/
def RegularGraph (N d : ℕ) : Type :=
  {G : SimpleGraph (Fin N) // G.IsRegularOfDegree d}

instance regularGraphFintype (N d : ℕ) : Fintype (RegularGraph N d) := by
  unfold RegularGraph
  infer_instance

namespace RegularGraph

variable {N d : ℕ}

def graph (g : RegularGraph N d) : SimpleGraph (Fin N) := g.1

theorem regular (g : RegularGraph N d) : g.graph.IsRegularOfDegree d := g.2

/-- A necessary admissibility identity, derived from the graph's degree sum. -/
theorem degree_sum (g : RegularGraph N d) :
    N * d = 2 * g.graph.edgeFinset.card := by
  calc
    N * d = ∑ v : Fin N, g.graph.degree v := by
      have hdeg : ∀ v, g.graph.degree v = d := g.regular
      simp [hdeg, nsmul_eq_mul]
    _ = 2 * g.graph.edgeFinset.card := g.graph.sum_degrees_eq_twice_card_edges

theorem admissible_even (g : RegularGraph N d) : Even (N * d) := by
  rw [g.degree_sum]
  exact even_two_mul _

/-- Uniform weights on the finite regular-graph ensemble. -/
def weight (_g : RegularGraph N d) : ℝ := finiteUniformWeight (RegularGraph N d) _g

theorem weight_nonnegative (g : RegularGraph N d) : 0 ≤ weight g :=
  finiteUniformWeight_nonneg g

theorem weight_normalized [Nonempty (RegularGraph N d)] :
    (∑ g : RegularGraph N d, weight g) = 1 := finiteUniformWeight_total

/-- The normalized physical adjacency matrix. -/
def H (g : RegularGraph N d) : Matrix (Fin N) (Fin N) ℂ := normalizedAdjacency g.graph d

def G (g : RegularGraph N d) (z : ℂ) : Matrix (Fin N) (Fin N) ℂ := green g.H z

/-- The oriented-edge average of the actual deleted-vertex resolvents. -/
def Q (g : RegularGraph N d) (z : ℂ) : ℂ := cavityAverage g.graph d z

/-- The minor is indexed by the actual remaining vertices. -/
def minorH (g : RegularGraph N d) (j : Fin N) :
    Matrix {i : Fin N // i ≠ j} {i : Fin N // i ≠ j} ℂ := deletedMatrix g.H j

def minorG (g : RegularGraph N d) (j : Fin N) (z : ℂ) :
    Matrix {i : Fin N // i ≠ j} {i : Fin N // i ≠ j} ℂ := green (g.minorH j) z

theorem H_hermitian (g : RegularGraph N d) : g.H.IsHermitian :=
  normalizedAdjacency_isHermitian g.graph d

theorem minorH_hermitian (g : RegularGraph N d) (j : Fin N) : (g.minorH j).IsHermitian :=
  deletedMatrix_isHermitian g.H g.H_hermitian j

theorem G_inverse (g : RegularGraph N d) (z : ℂ) (hz : 0 < z.im) :
    g.G z * spectralMatrix g.H z = 1 ∧ spectralMatrix g.H z * g.G z = 1 :=
  ⟨green_mul_spectralMatrix g.H g.H_hermitian z hz,
    spectralMatrix_mul_green g.H g.H_hermitian z hz⟩

theorem Q_im_nonnegative (g : RegularGraph N d) (z : ℂ) (hz : 0 < z.im) :
    0 ≤ (g.Q z).im := cavityAverage_im_nonneg g.graph d z hz

end RegularGraph

section Neighborhoods

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A radius-r induced ball, using infinite graph distance for disconnected
vertices. Thus unreachable vertices are excluded at every finite radius. -/
def graphBallVertices (G : SimpleGraph V) (o : V) (r : ℕ) : Set V :=
  {v | G.edist o v ≤ (r : ℕ∞)}

def graphBall (G : SimpleGraph V) (o : V) (r : ℕ) :
    SimpleGraph {v // v ∈ graphBallVertices G o r} := G.induce (graphBallVertices G o r)

omit [Fintype V] [DecidableEq V] in
theorem center_mem_graphBall (G : SimpleGraph V) (o : V) (r : ℕ) :
    o ∈ graphBallVertices G o r := by simp [graphBallVertices, G.edist_self]

omit [Fintype V] [DecidableEq V] in
theorem graphBallVertices_mono (G : SimpleGraph V) (o : V) {r R : ℕ} (h : r ≤ R) :
    graphBallVertices G o r ⊆ graphBallVertices G o R := by
  intro v hv
  change G.edist o v ≤ (r : ℕ∞) at hv
  change G.edist o v ≤ (R : ℕ∞)
  exact hv.trans (by exact_mod_cast h)

/-- The cyclomatic-number formula, with subtraction after adding edges and
components. It is never the incorrectly truncated expression E-V+C. -/
def graphExcess (G : SimpleGraph V) : ℕ :=
  G.edgeFinset.card + Nat.card G.ConnectedComponent - Fintype.card V

def graphBallExcess (G : SimpleGraph V) (o : V) (r : ℕ) : ℕ := graphExcess (graphBall G o r)

def nonTreeCenters (G : SimpleGraph V) (r : ℕ) : Finset V :=
  Finset.univ.filter (fun o => ¬ (graphBall G o r).IsTree)

/-- Finite, integer-parameter version of the paper's deterministic barOmega.
Applications specify the rounded radius and the allowed exceptional count. -/
def GraphTreeLike (G : SimpleGraph V) (R ω badCount : ℕ) : Prop :=
  (∀ o, graphBallExcess G o R ≤ ω) ∧ (nonTreeCenters G R).card ≤ badCount

omit [DecidableEq V] in
theorem nonTreeCenters_membership (G : SimpleGraph V) (r : ℕ) (o : V) :
    o ∈ nonTreeCenters G r ↔ ¬ (graphBall G o r).IsTree := by simp [nonTreeCenters]

/- The degree of an induced graph is bounded by the degree in the ambient
graph; the proof is the injection on neighbor sets. -/
omit [DecidableEq V] in
theorem induced_degree_le (G : SimpleGraph V) (S : Set V) (v : S) :
    (G.induce S).degree v ≤ G.degree v.val := by
  let f : (G.induce S).neighborSet v → G.neighborSet v.val := fun u => ⟨u.val.val, u.property⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun u : G.neighborSet v.val => u.val) hab
  have hcard := Fintype.card_le_of_injective f hf
  simpa only [SimpleGraph.card_neighborSet_eq_degree] using hcard

/-- The actual union of the two radius-r balls used by the entrywise model. -/
def pairBallVertices (G : SimpleGraph V) (i j : V) (r : ℕ) : Set V :=
  {v | G.edist i v ≤ (r : ℕ∞) ∨ G.edist j v ≤ (r : ℕ∞)}

def pairBallGraph (G : SimpleGraph V) (i j : V) (r : ℕ) :
    SimpleGraph {v // v ∈ pairBallVertices G i j r} := G.induce (pairBallVertices G i j r)

def pairBallLeft (G : SimpleGraph V) (i j : V) (r : ℕ) : pairBallVertices G i j r :=
  ⟨i, Or.inl (by simp [G.edist_self])⟩

def pairBallRight (G : SimpleGraph V) (i j : V) (r : ℕ) : pairBallVertices G i j r :=
  ⟨j, Or.inr (by simp [G.edist_self])⟩

end Neighborhoods

namespace RegularGraph

variable {N d : ℕ}

/-- The genuine induced-neighborhood boundary coefficient with zero deficit.
Missing degree is divided by d-1 exactly as in equation (2.11). -/
def pairBoundaryCoefficient (g : RegularGraph N d) (i j : Fin N) (r : ℕ)
    (v : pairBallVertices g.graph i j r) : ℝ :=
  ((d : ℝ) - ((pairBallGraph g.graph i j r).degree v : ℝ)) / ((d : ℝ) - 1)

theorem pairBoundaryCoefficient_nonnegative (g : RegularGraph N d) (hd : 3 ≤ d)
    (i j : Fin N) (r : ℕ) (v : pairBallVertices g.graph i j r) :
    0 ≤ g.pairBoundaryCoefficient i j r v := by
  have hdegree := induced_degree_le g.graph (pairBallVertices g.graph i j r) v
  rw [g.regular v.val] at hdegree
  have hreal : ((pairBallGraph g.graph i j r).degree v : ℝ) ≤ d := by
    exact_mod_cast hdegree
  unfold pairBoundaryCoefficient
  apply div_nonneg (by linarith)
  have hdc : (3 : ℝ) ≤ d := by exact_mod_cast hd
  linarith

/-- The actual finite pair-neighborhood extension Green function entry. -/
def P (g : RegularGraph N d) (r : ℕ) (z w : ℂ) (i j : Fin N) : ℂ :=
  boundaryGreen (normalizedAdjacency (pairBallGraph g.graph i j r) d)
    (Matrix.diagonal (fun v => (g.pairBoundaryCoefficient i j r v : ℂ))) w z
    (pairBallLeft g.graph i j r) (pairBallRight g.graph i j r)

/-- All inverses in the actual pair-neighborhood model are genuine inverses
in the upper-half-plane boundary domain. -/
theorem pairBoundaryMatrix_isUnit (g : RegularGraph N d) (hd : 3 ≤ d)
    (r : ℕ) (z w : ℂ) (hz : 0 < z.im) (hw : 0 ≤ w.im) (i j : Fin N) :
    IsUnit (boundaryMatrix (normalizedAdjacency (pairBallGraph g.graph i j r) d)
      (Matrix.diagonal (fun v => (g.pairBoundaryCoefficient i j r v : ℂ))) w z) :=
  boundaryMatrix_isUnit _ (normalizedAdjacency_isHermitian _ d)
    _ (g.pairBoundaryCoefficient_nonnegative hd i j r) w z hz hw

/-- In particular the actual random cavity boundary is in the admissible
finite-model domain; no model inverse hypothesis is added here. -/
theorem pairBoundaryMatrix_Q_isUnit (g : RegularGraph N d) (hd : 3 ≤ d)
    (r : ℕ) (z : ℂ) (hz : 0 < z.im) (i j : Fin N) :
    IsUnit (boundaryMatrix (normalizedAdjacency (pairBallGraph g.graph i j r) d)
      (Matrix.diagonal (fun v => (g.pairBoundaryCoefficient i j r v : ℂ))) (g.Q z) z) :=
  g.pairBoundaryMatrix_isUnit hd r z (g.Q z) hz (g.Q_im_nonnegative z hz) i j

/-- The physical reference boundary also gives a genuine finite-model inverse. -/
theorem pairBoundaryMatrix_reference_isUnit (g : RegularGraph N d) (hd : 3 ≤ d)
    (r : ℕ) (z : ℂ) (hz : 0 < z.im) (i j : Fin N) :
    IsUnit (boundaryMatrix (normalizedAdjacency (pairBallGraph g.graph i j r) d)
      (Matrix.diagonal (fun v => (g.pairBoundaryCoefficient i j r v : ℂ)))
      (semicircleRoot z) z) :=
  g.pairBoundaryMatrix_isUnit hd r z (semicircleRoot z) hz
    (semicircleRoot_im_pos hz).le i j

/-- The actual deterministic structural event in the regular-graph ensemble. -/
def structural (R ω badCount : ℕ) (g : RegularGraph N d) : Prop :=
  GraphTreeLike g.graph R ω badCount

end RegularGraph

/-- The physical algebraic semicircle branch. Integral identification is a
separate analytic theorem, not implicit in this definition. -/
def graphSemicircleReference (z : ℂ) : ℂ := semicircleRoot z

/-- The regular-tree diagonal reference associated to the physical branch. -/
def graphKestenMcKayReference (d : ℕ) (z : ℂ) : ℂ :=
  kestenMcKayTransform d (semicircleRoot z) z

end LocalLaw
