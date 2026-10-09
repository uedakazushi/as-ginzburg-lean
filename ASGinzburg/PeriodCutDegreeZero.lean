import ASGinzburg.PeriodCutGradedAlgebra
import ASGinzburg.FoundationAlgebra

/-! The actual degree-zero ring of the cut descent recovers the original
foundation ring, with its original unit and matrix multiplication. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
universe u v w
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k} {p : ℤ}
variable (E : A.PeriodIso p) {ι : Type w} [Fintype ι] (vertex : ι → ℤ)

noncomputable instance cutDegreeZeroAlgebra : Algebra k (E.CutGradedBlock vertex 0) :=
  Algebra.ofModule
    (fun c x y => by
      change E.cutBlockMul vertex 0 0 (c • x) y=c • E.cutBlockMul vertex 0 0 x y
      rw [map_smul,LinearMap.smul_apply])
    (fun c x y => by
      change E.cutBlockMul vertex 0 0 x (c • y)=c • E.cutBlockMul vertex 0 0 x y
      exact map_smul (E.cutBlockMul vertex 0 0 x) c y)

omit [Fintype ι] in
noncomputable def cutDegreeZeroComponentEquiv (i j : ι) :
    E.CutGradedHom 0 (vertex i) (vertex j) ≃ₗ[k] A.Hom (vertex i) (vertex j) :=
  A.homTransport (vertex i) (vertex j+(0:ℤ)*p) (vertex i) (vertex j) rfl (by ring)

omit [Fintype ι] in
theorem cutDegreeZeroComponent_comp {i j l : ι}
    (f : E.CutGradedHom 0 (vertex i) (vertex j))
    (g : E.CutGradedHom 0 (vertex j) (vertex l)) :
    E.cutDegreeZeroComponentEquiv vertex i l (E.cutGradedComp 0 0 g f)=
      A.comp (E.cutDegreeZeroComponentEquiv vertex j l g)
        (E.cutDegreeZeroComponentEquiv vertex i j f) := by
  rw [cutDegreeZeroComponentEquiv,cutGradedComp_apply,E.powNat_zero_apply,
    cutDegreeZeroComponentEquiv,cutDegreeZeroComponentEquiv]
  change A.homTransport (vertex i) (vertex l+(0:ℤ)*p) (vertex i) (vertex l) rfl _
    (A.homTransport (vertex i) ((vertex l+(0:ℤ)*p)+(0:ℤ)*p)
      (vertex i) (vertex l+(0:ℤ)*p) rfl _
      (A.comp (A.homTransport (vertex j) (vertex l+(0:ℤ)*p)
        (vertex j+(0:ℤ)*p) ((vertex l+(0:ℤ)*p)+(0:ℤ)*p) _ _ g) f))=
    A.comp (A.homTransport (vertex j) (vertex l+(0:ℤ)*p)
      (vertex j) (vertex l) rfl _ g)
      (A.homTransport (vertex i) (vertex j+(0:ℤ)*p) (vertex i) (vertex j) rfl _ f)
  rw [A.homTransport_trans,A.homTransport_comp _ _ _ (vertex i) (vertex j) (vertex l)
    rfl (by ring) (by ring),A.homTransport_trans]

section Foundation
variable {A : ZAlgebra.{u,u} k} {p : ℤ} (E : A.PeriodIso p) (Q : CutQuiver)

noncomputable def cutDegreeZeroFoundationLinearEquiv :
    E.CutGradedBlock (fun i : Q.Vertex => (i.val : ℤ)) 0 ≃ₗ[k] A.FoundationAlgebra Q :=
  LinearEquiv.piCongrRight fun i => LinearEquiv.piCongrRight fun j =>
    E.cutDegreeZeroComponentEquiv (fun i : Q.Vertex => (i.val : ℤ)) i j

theorem cutDegreeZeroFoundationLinearEquiv_apply
    (x : E.CutGradedBlock (fun i : Q.Vertex => (i.val : ℤ)) 0) (i j : Q.Vertex) :
    E.cutDegreeZeroFoundationLinearEquiv Q x i j=
      E.cutDegreeZeroComponentEquiv (fun i : Q.Vertex => (i.val : ℤ)) i j (x i j) := rfl

theorem cutDegreeZeroFoundationLinearEquiv_mul
    (x y : E.CutGradedBlock (fun i : Q.Vertex => (i.val : ℤ)) 0) :
    E.cutDegreeZeroFoundationLinearEquiv Q (x*y)=
      E.cutDegreeZeroFoundationLinearEquiv Q x * E.cutDegreeZeroFoundationLinearEquiv Q y := by
  funext i l
  change E.cutDegreeZeroComponentEquiv (fun i : Q.Vertex => (i.val : ℤ)) i l
    (E.cutBlockMul (fun i : Q.Vertex => (i.val : ℤ)) 0 0 x y i l)=_
  change E.cutDegreeZeroComponentEquiv (fun i : Q.Vertex => (i.val : ℤ)) i l
    (E.cutMatrixComp (fun i : Q.Vertex => (i.val : ℤ)) 0 0 x y i l)=_
  rw [cutMatrixComp_apply,map_sum,A.foundation_mul_component]
  apply Finset.sum_congr rfl
  intro j hj
  exact E.cutDegreeZeroComponent_comp (fun i : Q.Vertex => (i.val : ℤ)) (y i j) (x j l)

theorem cutDegreeZeroFoundationLinearEquiv_one :
    E.cutDegreeZeroFoundationLinearEquiv Q 1=(1 : A.FoundationAlgebra Q) := by
  classical
  funext i j
  change E.cutDegreeZeroComponentEquiv (fun i : Q.Vertex => (i.val : ℤ)) i j
    (E.cutMatrixId (fun i : Q.Vertex => (i.val : ℤ)) i j)=_
  by_cases h : i=j
  · subst j
    rw [cutMatrixId_diag,cutGradedId,cutDegreeZeroComponentEquiv]
    change A.homTransport (i.val : ℤ) ((i.val : ℤ)+(0:ℤ)*p) (i.val : ℤ) (i.val : ℤ)
      rfl _ (A.homTransport (i.val : ℤ) (i.val : ℤ) (i.val : ℤ)
        ((i.val : ℤ)+(0:ℤ)*p) rfl _ (A.id (i.val : ℤ)))=_
    rw [A.homTransport_trans]
    exact (A.foundation_one_diagonal Q i).symm
  · rw [E.cutMatrixId_offdiag _ h,map_zero]
    exact ((A.foundationComponents Q).totalOne_offdiag h).symm

noncomputable def cutDegreeZeroFoundationAlgEquiv :
    E.CutGradedBlock (fun i : Q.Vertex => (i.val : ℤ)) 0 ≃ₐ[k] A.FoundationAlgebra Q :=
  AlgEquiv.ofLinearEquiv (E.cutDegreeZeroFoundationLinearEquiv Q)
    (E.cutDegreeZeroFoundationLinearEquiv_one Q)
    (E.cutDegreeZeroFoundationLinearEquiv_mul Q)

end Foundation
end ASGinzburg.ZAlgebra.PeriodIso
