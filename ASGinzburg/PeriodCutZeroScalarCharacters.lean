import ASGinzburg.PeriodCutZeroNilpotence
import ASGinzburg.PeriodCutIdempotents

/-! Degree-zero characters factor through the genuine scalar diagonal,
because its kernel is concretely nilpotent. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

noncomputable def cutZeroRingInclusion :
    E.CutGradedBlock (fun t : Q.Vertex => (t.val:ℤ)) 0 →ₐ[k]
      E.CutGradedRing (fun t : Q.Vertex => (t.val:ℤ)) :=
  AlgHom.ofLinearMap (E.cutHomogeneousLinearInclusion (fun t : Q.Vertex => (t.val:ℤ)) 0)
    (E.cutHomogeneousInclusion_one _) (fun a b => (E.cutHomogeneousInclusion_mul _ 0 0 a b).symm)

theorem cutZeroScalarDiagonal_eq_sum (c : Q.Vertex→k) :
    E.cutZeroScalarDiagonal Q c=
      ∑ i : Q.Vertex,c i • E.cutMatrixComponent (fun t : Q.Vertex => (t.val:ℤ)) 0 i i
        (E.cutGradedId (i.val:ℤ)) := by
  classical
  funext r s
  simp only [Finset.sum_apply,Pi.smul_apply]
  rw [Finset.sum_eq_single r]
  · by_cases h : r=s
    · subst s
      simp [cutZeroScalarDiagonal]
    · simp [cutZeroScalarDiagonal,cutMatrixComponent,h,Ne.symm h]
  · intro i hi h
    rw [E.cutMatrixComponent_source_ne _ 0 i i r s _ (Ne.symm h),smul_zero]
  · simp

theorem cutZeroRingInclusion_scalarDiagonal (c : Q.Vertex→k) :
    E.cutZeroRingInclusion Q (E.cutZeroScalarDiagonal Q c)=
      ∑ i : Q.Vertex,c i • E.cutVertexIdempotent (fun t : Q.Vertex => (t.val:ℤ)) i := by
  rw [E.cutZeroScalarDiagonal_eq_sum,map_sum]
  simp only [map_smul]
  rfl

theorem cutCharacter_zeroDiagonal_eq_zero
    (χ : E.CutGradedRing (fun t : Q.Vertex => (t.val:ℤ)) →ₐ[k] k)
    (a : E.CutGradedBlock (fun t : Q.Vertex => (t.val:ℤ)) 0)
    (ha : E.cutZeroDiagonalAlgHom Q a=0) : χ (E.cutZeroRingInclusion Q a)=0 :=
  isNilpotent_iff_eq_zero.mp
    (((E.cutZeroKernel_isNilpotent Q a ha).map (E.cutZeroRingInclusion Q)).map χ)

theorem cutCharacter_zeroComponent_eq_diagonal
    (χ : E.CutGradedRing (fun t : Q.Vertex => (t.val:ℤ)) →ₐ[k] k) (i : Q.Vertex)
    (hvertex : ∀ j : Q.Vertex,χ (E.cutVertexIdempotent (fun t : Q.Vertex => (t.val:ℤ)) j)=
      if j=i then 1 else 0)
    (a : E.CutGradedBlock (fun t : Q.Vertex => (t.val:ℤ)) 0) :
    χ (E.cutZeroRingInclusion Q a)=E.cutZeroDiagonalAlgHom Q a i := by
  classical
  let c := E.cutZeroDiagonalAlgHom Q a
  have hzero : E.cutZeroDiagonalAlgHom Q (a-E.cutZeroScalarDiagonal Q c)=0 := by
    rw [map_sub,E.cutZeroDiagonalScalar_apply]
    exact sub_self _
  have h := E.cutCharacter_zeroDiagonal_eq_zero Q χ (a-E.cutZeroScalarDiagonal Q c) hzero
  rw [map_sub,map_sub,sub_eq_zero] at h
  rw [h,E.cutZeroRingInclusion_scalarDiagonal,map_sum]
  simp only [map_smul,hvertex,smul_eq_mul,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',
    Finset.mem_univ,if_true]
  rfl

end ASGinzburg.ZAlgebra.PeriodIso
