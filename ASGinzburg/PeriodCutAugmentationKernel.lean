import ASGinzburg.PeriodCutAugmentation
import ASGinzburg.PeriodCutCorners

/-! The augmentation kernel is exactly the elements with zero diagonal
in degree zero. The vertex idempotents map to their actual scalar coordinates. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

theorem cutAugmentation_linear_eq :
    (E.cutAugmentation Q).toLinearMap=
      (E.cutZeroDiagonalAlgHom Q).toLinearMap.comp
        (DirectSum.component k ℕ (E.CutGradedBlock (fun i : Q.Vertex => (i.val:ℤ))) 0) := by
  apply DirectSum.linearMap_ext
  intro m
  apply LinearMap.ext
  intro x
  change E.cutAugmentation Q
    (E.cutHomogeneousInclusion (fun i : Q.Vertex => (i.val:ℤ)) m x)=_
  rw [E.cutAugmentation_homogeneous]
  cases m with
  | zero => simp [cutAugmentationComponent]
  | succ m => simp [cutAugmentationComponent,DirectSum.component.of]

theorem cutAugmentation_apply
    (x : E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ))) :
    E.cutAugmentation Q x=E.cutZeroDiagonalAlgHom Q (x 0) :=
  LinearMap.congr_fun (E.cutAugmentation_linear_eq Q) x

theorem cutZeroDiagonal_eq_zero_iff
    (x : E.CutGradedBlock (fun i : Q.Vertex => (i.val:ℤ)) 0) :
    E.cutZeroDiagonalAlgHom Q x=0 ↔ ∀ i : Q.Vertex,x i i=0 := by
  constructor
  · intro h i
    have hi := congrFun h i
    change (A.scalarEndEquiv (i.val:ℤ)).symm
      (E.cutDegreeZeroComponentEquiv (fun i : Q.Vertex => (i.val:ℤ)) i i (x i i))=0 at hi
    apply (E.cutDegreeZeroComponentEquiv (fun i : Q.Vertex => (i.val:ℤ)) i i).injective
    apply (A.scalarEndEquiv (i.val:ℤ)).symm.injective
    simpa only [map_zero] using hi
  · intro h
    funext i
    change (A.scalarEndEquiv (i.val:ℤ)).symm
      (E.cutDegreeZeroComponentEquiv (fun i : Q.Vertex => (i.val:ℤ)) i i (x i i))=0
    rw [h i,map_zero,map_zero]

theorem mem_cutAugmentationKernel_iff
    (x : E.CutGradedRing (fun i : Q.Vertex => (i.val:ℤ))) :
    x∈E.cutAugmentationKernel Q ↔ ∀ i : Q.Vertex,x 0 i i=0 := by
  change E.cutAugmentation Q x=0 ↔ _
  rw [E.cutAugmentation_apply,E.cutZeroDiagonal_eq_zero_iff]

theorem cutAugmentation_vertexIdempotent (i : Q.Vertex) :
    E.cutAugmentation Q (E.cutVertexIdempotent (fun i : Q.Vertex => (i.val:ℤ)) i)=
      Pi.single i (1:k) := by
  classical
  rw [cutVertexIdempotent,E.cutAugmentation_zero_component]
  funext j
  change E.cutZeroDiagonalLinear Q
    (E.cutMatrixComponent (fun i : Q.Vertex => (i.val:ℤ)) 0 i i (E.cutGradedId (i.val:ℤ))) j=_
  rw [E.cutZeroDiagonalLinear_apply]
  by_cases h : j=i
  · subst j
    rw [E.cutMatrixComponent_apply_same]
    have h1 := congrFun (E.cutZeroDiagonalLinear_one Q) i
    rw [E.cutZeroDiagonalLinear_apply] at h1
    change (A.scalarEndEquiv (i.val:ℤ)).symm
      (E.cutDegreeZeroComponentEquiv (fun i : Q.Vertex => (i.val:ℤ)) i i
        (E.cutMatrixId (fun i : Q.Vertex => (i.val:ℤ)) i i))=1 at h1
    rw [E.cutMatrixId_diag] at h1
    simpa using h1
  · rw [E.cutMatrixComponent_source_ne (fun i : Q.Vertex => (i.val:ℤ))
      0 i i j j (E.cutGradedId (i.val:ℤ)) h,map_zero,map_zero]
    simp [h]

end ASGinzburg.ZAlgebra.PeriodIso
