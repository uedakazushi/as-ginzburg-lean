import ASGinzburg.FoundationAlgebra
import ASGinzburg.UnrolledPathPresentationMorphism

/-! Genuine vertex-fixing Z-algebra morphisms induce unital algebra
maps of the actual finite foundation blocks. -/
namespace ASGinzburg.ZAlgebra
universe u
variable {k : Type u} [Field k] {B A : ZAlgebra.{u,u} k}
  (F : Homomorphism B A) (Q : CutQuiver)

noncomputable def Homomorphism.foundationLinearMap :
    B.FoundationAlgebra Q →ₗ[k] A.FoundationAlgebra Q where
  toFun x i j := F.map (i.val : ℤ) (j.val : ℤ) (x i j)
  map_add' x y := by funext i j; exact (F.map _ _).map_add (x i j) (y i j)
  map_smul' c x := by funext i j; exact (F.map _ _).map_smul c (x i j)

theorem Homomorphism.foundationLinearMap_one : F.foundationLinearMap Q 1=1 := by
  classical
  funext i j
  change F.map (i.val : ℤ) (j.val : ℤ) ((B.foundationComponents Q).totalOne i j)=
    (A.foundationComponents Q).totalOne i j
  by_cases h : i=j
  · subst j
    rw [LinearComponentAlgebra.totalOne_diag,LinearComponentAlgebra.totalOne_diag]
    exact F.map_id (i.val : ℤ)
  · rw [LinearComponentAlgebra.totalOne_offdiag _ h,
      LinearComponentAlgebra.totalOne_offdiag _ h,map_zero]

theorem Homomorphism.foundationLinearMap_mul (x y : B.FoundationAlgebra Q) :
    F.foundationLinearMap Q (x*y)=F.foundationLinearMap Q x*F.foundationLinearMap Q y := by
  funext i l
  change F.map (i.val : ℤ) (l.val : ℤ) (∑ j : Q.Vertex,B.comp (x j l) (y i j))=
    ∑ j : Q.Vertex,A.comp (F.map (j.val : ℤ) (l.val : ℤ) (x j l))
      (F.map (i.val : ℤ) (j.val : ℤ) (y i j))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact F.map_comp (y i j) (x j l)

noncomputable def Homomorphism.foundationAlgebraMap :
    B.FoundationAlgebra Q →ₐ[k] A.FoundationAlgebra Q :=
  AlgHom.ofLinearMap (F.foundationLinearMap Q) (F.foundationLinearMap_one Q)
    (F.foundationLinearMap_mul Q)

theorem Homomorphism.foundationAlgebraMap_surjective
    (hF : ∀ i j,Function.Surjective (F.map i j)) :
    Function.Surjective (F.foundationAlgebraMap Q) := by
  intro x
  choose y hy using fun i j : Q.Vertex => hF (i.val : ℤ) (j.val : ℤ) (x i j)
  exact ⟨y,funext fun i => funext fun j => hy i j⟩

end ASGinzburg.ZAlgebra
