import ASGinzburg.ZAlgebraRightModuleSimples
import ASGinzburg.ZAlgebraRightModuleExtEquivalence
import ASGinzburg.ASRegular

/-! Intrinsic vertex-simple/representable Ext is preserved by an actual
vertex-fixing algebra isomorphism, with its original scalar action. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

noncomputable def rightModuleExtIsoCongr {M M' N N' : A.RightModule}
    (eM : M≅M') (eN : N≅N') (n : ℕ) :
    Abelian.Ext.{v} M N n ≃ₗ[k] Abelian.Ext.{v} M' N' n := by
  letI := HasDerivedCategory.standard A.RightModule
  letI : Linear k (DerivedCategory A.RightModule) := A.rightModuleDerivedLinear
  exact (A.rightModuleExtHomLinearEquiv M N n).trans
    ((ASGinzburg.derivedShiftedHomCongrLinearEquiv k
      ((DerivedCategory.singleFunctor A.RightModule 0).mapIso eM)
      ((DerivedCategory.singleFunctor A.RightModule 0).mapIso eN) (n:ℤ)).trans
        (A.rightModuleExtHomLinearEquiv M' N' n).symm)

namespace Isomorphism
variable {A B : ZAlgebra.{u,v} k} (E : Isomorphism A B)

noncomputable def vertexExtLinearEquiv (i j : ℤ) (n : ℕ) :
    Abelian.Ext.{v} (A.simpleRightModule i) (A.representable j) n ≃ₗ[k]
      Abelian.Ext.{v} (B.simpleRightModule i) (B.representable j) n :=
  (E.rightModuleExtLinearEquiv _ _ n).trans
    (B.rightModuleExtIsoCongr (E.rightModuleSimpleIso i) (E.rightModuleRepresentableIso j) n)

include E in
theorem asExtTotalRank_eq (Q : CutQuiver) (v : Q.LiftVertex) :
    A.asExtTotalRank Q v=B.asExtTotalRank Q v := by
  unfold ZAlgebra.asExtTotalRank
  congr 1
  funext n
  congr 1
  funext w
  exact (E.vertexExtLinearEquiv (Q.height w) (Q.height v) n).rank_eq

end Isomorphism
end ASGinzburg.ZAlgebra
