import ASGinzburg.ZAlgebraLinearEquivalence
import ASGinzburg.LinearRepresentationEquivalence
import ASGinzburg.EquivalenceProjectiveResolution
import ASGinzburg.ExactEquivalenceExt

/-! Actual algebra isomorphisms induce linear equivalences of the
original right-module categories, not only of their vertex categories. -/
namespace ASGinzburg.ZAlgebra.Isomorphism
open CategoryTheory
universe u v
variable {k : Type u} [Field k] {A B : ZAlgebra.{u,v} k}

instance linearEquivalenceOpFunctorAdditive (E : Isomorphism A B) :
    E.linearEquivalence.op.functor.Additive where
  map_add := by
    intro X Y f g
    change (E.linearFunctor.map (f.unop+g.unop)).op=
      (E.linearFunctor.map f.unop).op+(E.linearFunctor.map g.unop).op
    rw [Functor.map_add]
    rfl

instance linearEquivalenceOpFunctorLinear (E : Isomorphism A B) :
    E.linearEquivalence.op.functor.Linear k where
  map_smul := by
    intro X Y f c
    change (E.linearFunctor.map (c • f.unop)).op=
      c • (E.linearFunctor.map f.unop).op
    rw [Functor.map_smul]
    rfl

noncomputable def rightModuleEquivalence (E : Isomorphism A B) : A.RightModule ≌ B.RightModule :=
  linearRepresentationEquivalence (k:=k) E.linearEquivalence.op

instance rightModuleEquivalenceFunctorAdditive (E : Isomorphism A B) :
    E.rightModuleEquivalence.functor.Additive := by
  dsimp only [rightModuleEquivalence,linearRepresentationEquivalence]
  change (linearRepresentationPrecomposition (k:=k) E.linearEquivalence.op).Additive
  infer_instance

instance rightModuleEquivalenceFunctorLinear (E : Isomorphism A B) :
    E.rightModuleEquivalence.functor.Linear k := by
  dsimp only [rightModuleEquivalence,linearRepresentationEquivalence]
  change (linearRepresentationPrecomposition (k:=k) E.linearEquivalence.op).Linear k
  infer_instance

instance rightModuleEquivalenceInverseAdditive (E : Isomorphism A B) :
    E.rightModuleEquivalence.inverse.Additive := by infer_instance

instance rightModuleEquivalenceInverseLinear (E : Isomorphism A B) :
    E.rightModuleEquivalence.inverse.Linear k := by infer_instance

end ASGinzburg.ZAlgebra.Isomorphism
