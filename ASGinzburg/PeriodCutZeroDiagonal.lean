import ASGinzburg.PeriodCutDegreeZero
import ASGinzburg.PeriodCutMatrixComponents

/-! The degree-zero diagonal uses the genuine scalar endomorphisms and
preserves multiplication by directedness of the component algebra. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

noncomputable def cutZeroDiagonalLinear :
    E.CutGradedBlock (fun i : Q.Vertex => (i.val:ℤ)) 0 →ₗ[k] (Q.Vertex→k) :=
  { toFun := fun x i => (A.scalarEndEquiv (i.val:ℤ)).symm
      (E.cutDegreeZeroComponentEquiv (fun i : Q.Vertex => (i.val:ℤ)) i i (x i i))
    map_add' := by
      intro x y
      funext i
      change (A.scalarEndEquiv (i.val:ℤ)).symm
        (E.cutDegreeZeroComponentEquiv (fun i : Q.Vertex => (i.val:ℤ)) i i (x i i+y i i))=_
      rw [map_add,map_add]
      rfl
    map_smul' := by
      intro c x
      funext i
      change (A.scalarEndEquiv (i.val:ℤ)).symm
        (E.cutDegreeZeroComponentEquiv (fun i : Q.Vertex => (i.val:ℤ)) i i (c • x i i))=_
      rw [map_smul,map_smul]
      rfl }

theorem cutZeroDiagonalLinear_apply
    (x : E.CutGradedBlock (fun i : Q.Vertex => (i.val:ℤ)) 0) (i : Q.Vertex) :
    E.cutZeroDiagonalLinear Q x i=(A.scalarEndEquiv (i.val:ℤ)).symm
      (E.cutDegreeZeroComponentEquiv (fun i : Q.Vertex => (i.val:ℤ)) i i (x i i)) := rfl

theorem cutZeroComponent_product_diagonal
    (x y : E.CutGradedBlock (fun i : Q.Vertex => (i.val:ℤ)) 0) (i : Q.Vertex) :
    E.cutDegreeZeroComponentEquiv (fun i : Q.Vertex => (i.val:ℤ)) i i ((x*y) i i)=
      A.comp (E.cutDegreeZeroComponentEquiv (fun i : Q.Vertex => (i.val:ℤ)) i i (x i i))
        (E.cutDegreeZeroComponentEquiv (fun i : Q.Vertex => (i.val:ℤ)) i i (y i i)) := by
  change E.cutDegreeZeroComponentEquiv (fun i : Q.Vertex => (i.val:ℤ)) i i
    (E.cutMatrixComp (fun i : Q.Vertex => (i.val:ℤ)) 0 0 x y i i)=_
  rw [cutMatrixComp_apply,map_sum]
  rw [Finset.sum_eq_single i]
  · exact E.cutDegreeZeroComponent_comp _ _ _
  · intro j hj hji
    rw [E.cutDegreeZeroComponent_comp]
    have hv : j.val≠i.val := by intro h;apply hji;exact Fin.ext h
    rcases lt_or_gt_of_ne hv with hlt | hgt
    · have hz : E.cutDegreeZeroComponentEquiv (fun i : Q.Vertex => (i.val:ℤ)) i j (y i j)=0 :=
        A.positive (by omega) _
      rw [hz,map_zero]
    · have hz : E.cutDegreeZeroComponentEquiv (fun i : Q.Vertex => (i.val:ℤ)) j i (x j i)=0 :=
        A.positive (by omega) _
      rw [hz,map_zero,LinearMap.zero_apply]
  · simp

theorem cutZeroDiagonalLinear_one : E.cutZeroDiagonalLinear Q 1=1 := by
  funext i
  rw [E.cutZeroDiagonalLinear_apply]
  change (A.scalarEndEquiv (i.val:ℤ)).symm
    (E.cutDegreeZeroComponentEquiv (fun i : Q.Vertex => (i.val:ℤ)) i i
      (E.cutMatrixId (fun i : Q.Vertex => (i.val:ℤ)) i i))=1
  rw [E.cutMatrixId_diag,cutGradedId,cutDegreeZeroComponentEquiv]
  change (A.scalarEndEquiv (i.val:ℤ)).symm
    (A.homTransport (i.val:ℤ) ((i.val:ℤ)+(0:ℤ)*(Q.vertices:ℤ))
      (i.val:ℤ) (i.val:ℤ) rfl _
      (A.homTransport (i.val:ℤ) (i.val:ℤ) (i.val:ℤ)
        ((i.val:ℤ)+(0:ℤ)*(Q.vertices:ℤ)) rfl _ (A.id (i.val:ℤ))))=1
  rw [A.homTransport_trans]
  have h1 : A.scalarEndEquiv (i.val:ℤ) 1=A.id (i.val:ℤ) := by
    simp [ZAlgebra.scalarEndEquiv,LinearEquiv.ofBijective]
  change (A.scalarEndEquiv (i.val:ℤ)).symm (A.id (i.val:ℤ))=1
  rw [← h1,LinearEquiv.symm_apply_apply]

end ASGinzburg.ZAlgebra.PeriodIso
