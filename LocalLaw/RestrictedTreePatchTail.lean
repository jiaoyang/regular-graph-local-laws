import LocalLaw.RestrictedTreePatchReference
import LocalLaw.PhysicalModelLocalization

/-! # Pure exponential tree-patch errors for arbitrary old restrictions

No logarithmic diameter bound or ambient ball containment is required at
the physical boundary. Finite maxima supply a diameter and ordinary
feedback is exactly zero.
-/

noncomputable section
namespace LocalLaw
local instance restrictedTreePatchTailDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace DeficientGraph
variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

theorem restrict_tree_diagonal_physical_tail (g : DeficientGraph V d) (hd : 3≤d)
    (S : Set V) (hbudget : (g.restrict S).ComponentFiniteReferenceBudget)
    (root : S) (r : ℕ) (htree : (graphBall g.graph root.val r).IsTree)
    (hzero : ∀ v∈graphBallVertices g.graph root.val r,g.deficit v=0) (z : ℂ) (hz : 0<z.im) :
    ‖(g.restrict S).extensionGreen (semicircleRoot z) z root root-graphKestenMcKayReference d z‖≤
      physicalModelTailConstant d*physicalTransfer d z^(2*r) := by
  let M := g.restrict S
  let R := Finset.univ.sup (fun ij : S×S => M.graph.dist ij.1 ij.2)
  have hR (i j : S) : M.graph.dist i j≤R := Finset.le_sup (f:=fun ij : S×S => M.graph.dist ij.1 ij.2) (Finset.mem_univ (i,j))
  have hh := M.physical_pair_localization hd hbudget R r hR z hz root root
  have hP : M.P r z (semicircleRoot z) root root=graphKestenMcKayReference d z :=
    g.restrict_P_diagonal_of_ambient_tree hd S root r htree hzero (semicircleRoot z) z
      (semicircleRoot_equation z) hz (semicircleRoot_im_pos hz).le
  rw [hP] at hh
  exact hh

theorem restrict_tree_adjacent_physical_tail (g : DeficientGraph V d) (hd : 3≤d)
    (S : Set V) (hbudget : (g.restrict S).ComponentFiniteReferenceBudget)
    (u v : S) (huv : g.graph.Adj u.val v.val) (r : ℕ)
    (htree : (graphBall g.graph u.val (r+1)).IsTree)
    (hzero : ∀ w∈graphBallVertices g.graph u.val (r+1),g.deficit w=0) (z : ℂ) (hz : 0<z.im) :
    ‖(g.restrict S).extensionGreen (semicircleRoot z) z u v-
        graphKestenMcKayReference d z*(-semicircleRoot z*treeEdgeWeight d)‖≤
      physicalModelTailConstant d*physicalTransfer d z^(2*r) := by
  let M := g.restrict S
  let R := Finset.univ.sup (fun ij : S×S => M.graph.dist ij.1 ij.2)
  have hR (i j : S) : M.graph.dist i j≤R := Finset.le_sup (f:=fun ij : S×S => M.graph.dist ij.1 ij.2) (Finset.mem_univ (i,j))
  have hh := M.physical_pair_localization hd hbudget R r hR z hz u v
  have hP : M.P r z (semicircleRoot z) u v=graphKestenMcKayReference d z*(-semicircleRoot z*treeEdgeWeight d) :=
    g.restrict_P_adjacent_of_ambient_tree hd S u v huv r htree hzero (semicircleRoot z) z
      (semicircleRoot_equation z) hz (semicircleRoot_im_pos hz).le
  rw [hP] at hh
  exact hh

end DeficientGraph
end LocalLaw
