import LocalLaw.CavityTreeFeedback
import LocalLaw.BlockSchur

/-!
# Exact vacuum compensation for one attached finite cavity tree

The root of any actual one-deficit finite tree has diagonal Green value
m_sc. Its one-edge self-energy is m_sc/(d-1), exactly canceling the boundary
charge gained when the branch is removed. No homogeneous-depth assumption
or final Schur identity is supplied.
-/
noncomputable section
namespace LocalLaw
local instance treeVacuumSchurDecidable (p : Prop) : Decidable p := Classical.propDecidable p
namespace DeficientGraph
variable {J : Type} [Fintype J] [DecidableEq J] {d : ℕ}

theorem one_root_tree_physical_diagonal (g : DeficientGraph J d) (hd : 3≤d)
    (hTree : g.graph.IsTree) (root : J)
    (hdeficit : ∀ v,g.deficit v=if v=root then 1 else 0) (z : ℂ) (hz : 0<z.im) :
    g.extensionGreen (semicircleRoot z) z root root=semicircleRoot z := by
  have hdeg : ∀ v,g.graph.degree v+(if v=root then 1 else 0)≤d := by
    intro v
    simpa only [hdeficit v] using g.degree_deficit_le v
  change (g.extensionMatrix (semicircleRoot z) z)⁻¹ root root=semicircleRoot z
  rw [g.extensionMatrix_one_root_deficit root hdeficit]
  exact forestReference_cavity_diagonal g.graph hTree.IsAcyclic d hd root hdeg (semicircleRoot z) z
    (semicircleRoot_equation z) hz (semicircleRoot_im_pos hz).le

end DeficientGraph

section Attachment
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def treeVacuumCoupling (d : ℕ) (b : I) (root : J) : Matrix I J ℂ :=
  fun i j=>if i=b ∧ j=root then treeEdgeWeight d else 0

def treeVacuumCharge (d : ℕ) (b : I) (m : ℂ) : Matrix I I ℂ :=
  Matrix.diagonal (fun i=>if i=b then m/((d:ℂ)-1) else 0)

omit [Fintype I] in
theorem treeVacuum_selfEnergy (d : ℕ) (hd : 3≤d) (b : I)
    (g : DeficientGraph J d) (hTree : g.graph.IsTree) (root : J)
    (hdeficit : ∀ v,g.deficit v=if v=root then 1 else 0) (z : ℂ) (hz : 0<z.im) :
    treeVacuumCoupling d b root*g.extensionGreen (semicircleRoot z) z*(treeVacuumCoupling d b root).transpose=
      treeVacuumCharge d b (semicircleRoot z) := by
  have hroot:=g.one_root_tree_physical_diagonal hd hTree root hdeficit z hz
  ext i j
  by_cases hi : i=b <;> by_cases hj : j=b
  · subst i; subst j
    simp only [Matrix.mul_apply,treeVacuumCoupling,Matrix.transpose_apply,treeVacuumCharge,
      Matrix.diagonal_apply,if_pos rfl,and_true,true_and,ite_mul,zero_mul,mul_ite,mul_zero,
      Finset.sum_ite_eq',Finset.mem_univ,if_true]
    rw [hroot]
    have he:=treeEdgeWeight_sq d hd
    calc
      _ = treeEdgeWeight d^2*semicircleRoot z := by ring
      _ = _ := by rw [he]; ring
  · simp [Matrix.mul_apply,treeVacuumCoupling,Matrix.transpose_apply,treeVacuumCharge,Matrix.diagonal_apply,hi,hj,Ne.symm hj]
  · simp [Matrix.mul_apply,treeVacuumCoupling,Matrix.transpose_apply,treeVacuumCharge,Matrix.diagonal_apply,hi,hj]
  · simp [Matrix.mul_apply,treeVacuumCoupling,Matrix.transpose_apply,treeVacuumCharge,Matrix.diagonal_apply,hi,hj]

/-- A concrete attached-tree block matrix is invertible and has exactly
the retained Green block, because its tree self-energy cancels its charge. -/
theorem treeVacuum_retained_inverse (d : ℕ) (hd : 3≤d) (A : Matrix I I ℂ) (hA : IsUnit A)
    (b : I) (g : DeficientGraph J d) (hTree : g.graph.IsTree) (root : J)
    (hdeficit : ∀ v,g.deficit v=if v=root then 1 else 0) (z : ℂ) (hz : 0<z.im) :
    let C:=treeVacuumCoupling d b root
    let M:=Matrix.fromBlocks (A+treeVacuumCharge d b (semicircleRoot z)) C C.transpose
      (g.extensionMatrix (semicircleRoot z) z)
    IsUnit M ∧ (M⁻¹).toBlocks₁₁=A⁻¹ := by
  dsimp only
  let C:=treeVacuumCoupling d b root
  let B:=g.extensionMatrix (semicircleRoot z) z
  let D:=treeVacuumCharge d b (semicircleRoot z)
  let M:=Matrix.fromBlocks (A+D) C C.transpose B
  have hB : IsUnit B:=g.extensionMatrix_isUnit hd (semicircleRoot z) z hz (semicircleRoot_im_pos hz).le
  have hself : C*B⁻¹*C.transpose=D := treeVacuum_selfEnergy d hd b g hTree root hdeficit z hz
  have hSchur : blockSchur M=A := by
    change A+D-C*B⁻¹*C.transpose=A
    rw [hself]
    abel
  have hM : IsUnit M := by
    letI : Invertible B:=Classical.choice hB.nonempty_invertible
    apply Matrix.isUnit_fromBlocks_iff_of_invertible₂₂.mpr
    change IsUnit (A+D-C*⅟ B*C.transpose)
    rw [Matrix.invOf_eq_nonsing_inv,hself]
    simpa only [add_sub_cancel_right] using hA
  exact ⟨hM,by rw [inverse_block11 M hM hB,hSchur]⟩

end Attachment
end LocalLaw
