import work.ASGinzburgDraft.TriangleGLWordArrowCoefficients
import Mathlib.Logic.Equiv.Fin.Basic

/-! The actual nine-arrow GL coefficient matrix has the actual inverse
given by the three inverse arrow matrices. -/
namespace ASGinzburg
universe u v
variable (k : Type u) [Field k]

theorem triangleEdgeArrow_source (s i : Fin 3) : triangle333.source (triangleEdgeArrow s i) = s := by
  apply Fin.ext
  dsimp [triangle333,triangleEdgeArrow]
  omega

theorem triangleEdgeArrow_index (s i : Fin 3) : triangleGLArrowIndex (triangleEdgeArrow s i) = i := by
  apply Fin.ext
  dsimp [triangleGLArrowIndex,triangleEdgeArrow]
  omega

theorem triangleArrow_eq_iff_source_index (a b : triangle333.Arrow) :
    a = b ↔ triangle333.source a = triangle333.source b ∧
      triangleGLArrowIndex a = triangleGLArrowIndex b := by
  constructor
  · intro h
    simp [h]
  · rintro ⟨hs,hi⟩
    have hs' := congrArg Fin.val hs
    have hi' := congrArg Fin.val hi
    apply Fin.ext
    dsimp [triangle333,triangleGLArrowIndex] at hs' hi'
    omega

theorem triangleArrow_sum {M : Type v} [AddCommMonoid M] (f : triangle333.Arrow → M) :
    (∑ a : triangle333.Arrow, f a) =
      ∑ s : Fin 3, ∑ i : Fin 3, f (triangleEdgeArrow s i) := by
  classical
  have h : ∀ p : Fin 3 × Fin 3,
      (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9) p = triangleEdgeArrow p.1 p.2 := by
    intro p
    apply Fin.ext
    simp [finProdFinEquiv,triangleEdgeArrow,Nat.add_comm]
  have result := (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).sum_comp f
  simp_rw [h] at result
  simpa only [Fintype.sum_prod_type] using result.symm

theorem finitePiLinearEquiv_matrix_inverse_sum {I : Type v} [Fintype I] [DecidableEq I]
    (g : (I → k) ≃ₗ[k] (I → k)) (a b : I) :
    (∑ i : I, g (Pi.single a 1) i * g.symm (Pi.single i 1) b) =
      (Pi.single a (1 : k) : I → k) b := by
  classical
  have he : g (Pi.single a 1) =
      ∑ i : I, g (Pi.single a 1) i • (Pi.single i (1 : k) : I → k) := by
    simpa only [Pi.basisFun_repr,Pi.basisFun_apply] using
      ((Pi.basisFun k I).sum_repr (g (Pi.single a 1))).symm
  have h := congrArg (fun x : I → k => g.symm x b) he
  simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,
    LinearEquiv.symm_apply_apply] at h
  exact h.symm

theorem triangleGLWordArrowCoefficient_inverse_sum (g : TriangleGL333 k)
    (a b : triangle333.Arrow) :
    (∑ i : triangle333.Arrow,
      triangleGLWordArrowCoefficient k g a i * triangleGLWordArrowCoefficient k (g⁻¹) i b) =
        if a = b then 1 else 0 := by
  classical
  rw [triangleArrow_sum]
  have hOnly : (∑ s : Fin 3, ∑ i : Fin 3,
      triangleGLWordArrowCoefficient k g a (triangleEdgeArrow s i) *
        triangleGLWordArrowCoefficient k (g⁻¹) (triangleEdgeArrow s i) b) =
      ∑ i : Fin 3, triangleGLWordArrowCoefficient k g a
        (triangleEdgeArrow (triangle333.source a) i) *
          triangleGLWordArrowCoefficient k (g⁻¹)
            (triangleEdgeArrow (triangle333.source a) i) b := by
    apply Finset.sum_eq_single (triangle333.source a)
    · intro s hs hsa
      apply Finset.sum_eq_zero
      intro i hi
      simp [triangleGLWordArrowCoefficient,triangleEdgeArrow_source,hsa]
    · simp
  rw [hOnly]
  by_cases hba : triangle333.source b = triangle333.source a
  · simp only [triangleGLWordArrowCoefficient,triangleEdgeArrow_source,
      triangleEdgeArrow_index,hba,ite_true,triangleGLArrowMatrix_inv]
    rw [finitePiLinearEquiv_matrix_inverse_sum k]
    have hidx : triangleGLArrowIndex b = triangleGLArrowIndex a ↔ a = b := by
      constructor
      · intro h
        exact (triangleArrow_eq_iff_source_index a b).mpr ⟨hba.symm,h.symm⟩
      · intro h
        rw [h]
    simp only [Pi.single_apply,hidx]
  · have hab : a ≠ b := by
      intro h
      apply hba
      rw [h]
    simp [triangleGLWordArrowCoefficient,triangleEdgeArrow_source,hba,hab]

end ASGinzburg
