import ASGinzburg.RegularRightModule

/-! Every total algebra element acts on the concrete right regular module by
actual left multiplication, as a morphism of unitized right modules. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)
noncomputable def totalAlgebraLeftMap (a : A.totalAlgebra) :
    A.totalAlgebraRightLocallyUnitalModule ⟶ A.totalAlgebraRightLocallyUnitalModule :=
  A.rightRegularTotalLocallyUnitalIso.inv ≫
    A.rightTotalLocallyUnitalFunctor.map (a : CategoryTheory.End A.rightRegularCoproduct) ≫
      A.rightRegularTotalLocallyUnitalIso.hom

@[simp] theorem totalAlgebraLeftMap_component {i j : ℤ} (a : A.Hom i j) :
    A.totalAlgebraLeftMap (A.totalAlgebraComponent a) = A.totalAlgebraLeftComponentMap a := by
  dsimp only [totalAlgebraLeftMap]
  rw [A.totalAlgebraComponent_coe]
  rfl

theorem totalAlgebraLeftMap_add (a b : A.totalAlgebra) :
    A.totalAlgebraLeftMap (a + b) = A.totalAlgebraLeftMap a + A.totalAlgebraLeftMap b := by
  change _ ≫ A.rightTotalLocallyUnitalFunctor.map
    ((a : CategoryTheory.End A.rightRegularCoproduct) + (b : CategoryTheory.End A.rightRegularCoproduct)) ≫ _ = _
  rw [Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]
  rfl

theorem totalAlgebraLeftMap_zero : A.totalAlgebraLeftMap 0 = 0 := by
  change _ ≫ A.rightTotalLocallyUnitalFunctor.map (0 : CategoryTheory.End A.rightRegularCoproduct) ≫ _ = 0
  rw [Functor.map_zero, zero_comp, comp_zero]

theorem totalAlgebraLeftMap_apply (a : A.totalAlgebra) (x : A.totalAlgebra) :
    (A.totalAlgebraLeftMap a).hom x = a * x := by
  obtain ⟨a,rfl⟩ := A.totalAlgebraEquiv.surjective a
  induction a using DFinsupp.induction with
  | h0 => rw [map_zero, A.totalAlgebraLeftMap_zero]; rfl
  | ha p b a _ _ ih =>
    rw [map_add, A.totalAlgebraLeftMap_add, ModuleCat.hom_add, LinearMap.add_apply, add_mul, ih]
    congr 1
    rcases p with ⟨i,j⟩
    change (A.totalAlgebraLeftMap (A.totalAlgebraComponent b)).hom x =
      A.totalAlgebraComponent b * x
    rw [A.totalAlgebraLeftMap_component]
    exact A.totalAlgebraLeftComponentMap_apply b x

end ASGinzburg.ZAlgebra
