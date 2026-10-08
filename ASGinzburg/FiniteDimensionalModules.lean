import ASGinzburg.TotalModuleSpaces
import ASGinzburg.ASLeftExtReciprocity
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Category.ModuleCat.Free

namespace ASGinzburg
open scoped DirectSum
universe u v w
variable {k : Type u} [Field k] {I : Type w} (V : I → Type v)
  [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]

theorem directSum_finite_support_of_finite [Module.Finite k (⨁ i, V i)] :
    ∃ S : Finset I, ∀ i, i ∉ S → ∀ x : V i, x = 0 := by
  classical
  let b := Module.finBasis k (⨁ i, V i)
  let S := Finset.univ.biUnion (fun j => (b j).support)
  refine ⟨S,?_⟩
  intro i hi x
  have hb : ∀ j, i ∉ (b j).support := by
    intro j hj
    apply hi
    exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ j,hj⟩
  have hp : DirectSum.component k I V i = 0 := by
    apply b.ext
    intro j
    change (b j) i = 0
    exact DFinsupp.notMem_support_iff.mp (hb j)
  have hx := LinearMap.congr_fun hp (DirectSum.lof k I V i x)
  simpa using hx
end ASGinzburg

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

def rightFiniteDimensionalProperty : ObjectProperty A.RightModule :=
  fun M => Module.Finite k (A.rightModuleTotalSpace M)

def leftFiniteDimensionalProperty : ObjectProperty A.LeftModule :=
  fun M => Module.Finite k (A.leftModuleTotalSpace M)

theorem rightFiniteDimensional_finite_support {M : A.RightModule}
    (h : A.rightFiniteDimensionalProperty M) :
    ∃ S : Finset ℤ, ∀ i, i ∉ S → IsZero ((A.rightModuleEvaluation i).obj M) := by
  letI : Module.Finite k (A.rightModuleTotalSpace M) := h
  obtain ⟨S,hS⟩ := ASGinzburg.directSum_finite_support_of_finite (k := k)
    (fun i => (A.rightModuleEvaluation i).obj M)
  refine ⟨S,fun i hi => ModuleCat.isZero_iff_subsingleton.mpr ?_⟩
  exact ⟨fun x y => by rw [hS i hi x,hS i hi y]⟩

theorem leftFiniteDimensional_finite_support {M : A.LeftModule}
    (h : A.leftFiniteDimensionalProperty M) :
    ∃ S : Finset ℤ, ∀ i, i ∉ S → IsZero ((A.leftModuleEvaluation i).obj M) := by
  letI : Module.Finite k (A.leftModuleTotalSpace M) := h
  obtain ⟨S,hS⟩ := ASGinzburg.directSum_finite_support_of_finite (k := k)
    (fun i => (A.leftModuleEvaluation i).obj M)
  refine ⟨S,fun i hi => ModuleCat.isZero_iff_subsingleton.mpr ?_⟩
  exact ⟨fun x y => by rw [hS i hi x,hS i hi y]⟩

theorem rightFiniteDimensional_of_mono {M N : A.RightModule} (f : M ⟶ N) [Mono f]
    (hN : A.rightFiniteDimensionalProperty N) : A.rightFiniteDimensionalProperty M := by
  letI : Module.Finite k (A.rightModuleTotalSpace N) := hN
  letI : Module.Finite k (A.rightModuleTotalFunctor.obj N) :=
    Module.Finite.equiv (A.rightModuleTotalFunctorObjIso N).symm.toLinearEquiv
  have hM : Module.Finite k (A.rightModuleTotalFunctor.obj M) :=
    FiniteDimensional.of_injective (A.rightModuleTotalFunctor.map f).hom
      ((ModuleCat.mono_iff_injective _).mp (by infer_instance))
  letI := hM
  exact Module.Finite.equiv (A.rightModuleTotalFunctorObjIso M).toLinearEquiv

theorem rightFiniteDimensional_of_epi {M N : A.RightModule} (f : M ⟶ N) [Epi f]
    (hM : A.rightFiniteDimensionalProperty M) : A.rightFiniteDimensionalProperty N := by
  letI : Module.Finite k (A.rightModuleTotalSpace M) := hM
  letI : Module.Finite k (A.rightModuleTotalFunctor.obj M) :=
    Module.Finite.equiv (A.rightModuleTotalFunctorObjIso M).symm.toLinearEquiv
  have hN : Module.Finite k (A.rightModuleTotalFunctor.obj N) :=
    Module.Finite.of_surjective (A.rightModuleTotalFunctor.map f).hom
      ((ModuleCat.epi_iff_surjective _).mp (by infer_instance))
  letI := hN
  exact Module.Finite.equiv (A.rightModuleTotalFunctorObjIso N).toLinearEquiv

theorem rightFiniteDimensional_bounded_support {M : A.RightModule}
    (h : A.rightFiniteDimensionalProperty M) :
    ∃ a b : ℤ, ∀ i, i < a ∨ b < i → IsZero ((A.rightModuleEvaluation i).obj M) := by
  obtain ⟨S,hS⟩ := A.rightFiniteDimensional_finite_support h
  obtain ⟨a,ha⟩ := S.bddBelow
  obtain ⟨b,hb⟩ := S.bddAbove
  refine ⟨a,b,fun i hi => hS i ?_⟩
  intro himem
  have hia : a ≤ i := ha himem
  have hib : i ≤ b := hb himem
  omega

theorem leftFiniteDimensional_of_mono {M N : A.LeftModule} (f : M ⟶ N) [Mono f]
    (hN : A.leftFiniteDimensionalProperty N) : A.leftFiniteDimensionalProperty M := by
  letI : Module.Finite k (A.leftModuleTotalSpace N) := hN
  letI : Module.Finite k (A.leftModuleTotalFunctor.obj N) :=
    Module.Finite.equiv (A.leftModuleTotalFunctorObjIso N).symm.toLinearEquiv
  have hM : Module.Finite k (A.leftModuleTotalFunctor.obj M) :=
    FiniteDimensional.of_injective (A.leftModuleTotalFunctor.map f).hom
      ((ModuleCat.mono_iff_injective _).mp (by infer_instance))
  letI := hM
  exact Module.Finite.equiv (A.leftModuleTotalFunctorObjIso M).toLinearEquiv

theorem leftFiniteDimensional_of_epi {M N : A.LeftModule} (f : M ⟶ N) [Epi f]
    (hM : A.leftFiniteDimensionalProperty M) : A.leftFiniteDimensionalProperty N := by
  letI : Module.Finite k (A.leftModuleTotalSpace M) := hM
  letI : Module.Finite k (A.leftModuleTotalFunctor.obj M) :=
    Module.Finite.equiv (A.leftModuleTotalFunctorObjIso M).symm.toLinearEquiv
  have hN : Module.Finite k (A.leftModuleTotalFunctor.obj N) :=
    Module.Finite.of_surjective (A.leftModuleTotalFunctor.map f).hom
      ((ModuleCat.epi_iff_surjective _).mp (by infer_instance))
  letI := hN
  exact Module.Finite.equiv (A.leftModuleTotalFunctorObjIso N).toLinearEquiv

theorem leftFiniteDimensional_bounded_support {M : A.LeftModule}
    (h : A.leftFiniteDimensionalProperty M) :
    ∃ a b : ℤ, ∀ i, i < a ∨ b < i → IsZero ((A.leftModuleEvaluation i).obj M) := by
  obtain ⟨S,hS⟩ := A.leftFiniteDimensional_finite_support h
  obtain ⟨a,ha⟩ := S.bddBelow
  obtain ⟨b,hb⟩ := S.bddAbove
  refine ⟨a,b,fun i hi => hS i ?_⟩
  intro himem
  have hia : a ≤ i := ha himem
  have hib : i ≤ b := hb himem
  omega
end ASGinzburg.ZAlgebra

namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k]

theorem moduleCat_finite_of_shortExact {S : ShortComplex (ModuleCat.{v} k)}
    (hS : S.ShortExact) [Module.Finite k S.X₁] [Module.Finite k S.X₃] :
    Module.Finite k S.X₂ :=
  Module.Finite.of_basis
    (ModuleCat.Basis.ofShortExact hS (Module.finBasis k S.X₁) (Module.finBasis k S.X₃))
end ASGinzburg

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

theorem rightFiniteDimensional_of_shortExact {S : ShortComplex A.RightModule}
    (hS : S.ShortExact) (h₁ : A.rightFiniteDimensionalProperty S.X₁)
    (h₃ : A.rightFiniteDimensionalProperty S.X₃) : A.rightFiniteDimensionalProperty S.X₂ := by
  letI := hS.mono_f
  letI := hS.epi_g
  letI : Module.Finite k (A.rightModuleTotalSpace S.X₁) := h₁
  letI : Module.Finite k (A.rightModuleTotalSpace S.X₃) := h₃
  letI : Module.Finite k (A.rightModuleTotalFunctor.obj S.X₁) :=
    Module.Finite.equiv (A.rightModuleTotalFunctorObjIso S.X₁).symm.toLinearEquiv
  letI : Module.Finite k (A.rightModuleTotalFunctor.obj S.X₃) :=
    Module.Finite.equiv (A.rightModuleTotalFunctorObjIso S.X₃).symm.toLinearEquiv
  letI : Module.Finite k (S.map A.rightModuleTotalFunctor).X₁ := by
    change Module.Finite k (A.rightModuleTotalFunctor.obj S.X₁)
    infer_instance
  letI : Module.Finite k (S.map A.rightModuleTotalFunctor).X₃ := by
    change Module.Finite k (A.rightModuleTotalFunctor.obj S.X₃)
    infer_instance
  letI : Module.Finite k (A.rightModuleTotalFunctor.obj S.X₂) :=
    ASGinzburg.moduleCat_finite_of_shortExact
      (S := S.map A.rightModuleTotalFunctor) (hS.map A.rightModuleTotalFunctor)
  exact Module.Finite.equiv (A.rightModuleTotalFunctorObjIso S.X₂).toLinearEquiv

theorem rightFiniteDimensional_simple (i : ℤ) :
    A.rightFiniteDimensionalProperty (A.simpleRightModule i) := by
  classical
  let V : ℤ → Type v := fun j => (A.rightModuleEvaluation j).obj (A.simpleRightModule i)
  letI : Module.Finite k ((A.rightModuleEvaluation i).obj (A.representable i)) :=
    show Module.Finite k (A.Hom i i) from inferInstance
  letI : Module.Finite k (V i) :=
    Module.Finite.equiv (A.simpleRightModuleDiagonalIso i).symm.toLinearEquiv
  apply FiniteDimensional.of_injective (DirectSum.component k ℤ V i)
  intro x y hxy
  apply DFinsupp.ext
  intro j
  by_cases hj : j = i
  · subst j
    exact hxy
  · exact (ModuleCat.isZero_iff_subsingleton.mp (A.simpleRightModule_off_diagonal i j hj)).elim _ _
end ASGinzburg.ZAlgebra

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

theorem leftFiniteDimensional_of_shortExact {S : ShortComplex A.LeftModule}
    (hS : S.ShortExact) (h₁ : A.leftFiniteDimensionalProperty S.X₁)
    (h₃ : A.leftFiniteDimensionalProperty S.X₃) : A.leftFiniteDimensionalProperty S.X₂ := by
  letI := hS.mono_f
  letI := hS.epi_g
  letI : Module.Finite k (A.leftModuleTotalSpace S.X₁) := h₁
  letI : Module.Finite k (A.leftModuleTotalSpace S.X₃) := h₃
  letI : Module.Finite k (A.leftModuleTotalFunctor.obj S.X₁) :=
    Module.Finite.equiv (A.leftModuleTotalFunctorObjIso S.X₁).symm.toLinearEquiv
  letI : Module.Finite k (A.leftModuleTotalFunctor.obj S.X₃) :=
    Module.Finite.equiv (A.leftModuleTotalFunctorObjIso S.X₃).symm.toLinearEquiv
  letI : Module.Finite k (S.map A.leftModuleTotalFunctor).X₁ := by
    change Module.Finite k (A.leftModuleTotalFunctor.obj S.X₁)
    infer_instance
  letI : Module.Finite k (S.map A.leftModuleTotalFunctor).X₃ := by
    change Module.Finite k (A.leftModuleTotalFunctor.obj S.X₃)
    infer_instance
  letI : Module.Finite k (A.leftModuleTotalFunctor.obj S.X₂) :=
    ASGinzburg.moduleCat_finite_of_shortExact
      (S := S.map A.leftModuleTotalFunctor) (hS.map A.leftModuleTotalFunctor)
  exact Module.Finite.equiv (A.leftModuleTotalFunctorObjIso S.X₂).toLinearEquiv

theorem leftFiniteDimensional_simple (i : ℤ) :
    A.leftFiniteDimensionalProperty (A.simpleLeftModule i) := by
  classical
  let V : ℤ → Type v := fun j => (A.leftModuleEvaluation j).obj (A.simpleLeftModule i)
  letI : Module.Finite k ((A.leftModuleEvaluation i).obj (A.leftRepresentable i)) :=
    show Module.Finite k (A.Hom i i) from inferInstance
  letI : Module.Finite k (V i) :=
    Module.Finite.equiv (A.simpleLeftModuleDiagonalIso i).symm.toLinearEquiv
  apply FiniteDimensional.of_injective (DirectSum.component k ℤ V i)
  intro x y hxy
  apply DFinsupp.ext
  intro j
  by_cases hj : j = i
  · subst j
    exact hxy
  · exact (ModuleCat.isZero_iff_subsingleton.mp (A.simpleLeftModule_off_diagonal i j hj)).elim _ _
end ASGinzburg.ZAlgebra

namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{v} C]

theorem ext_eq_zero_of_isZero_source {M N : C} (hM : IsZero M) (n : ℕ)
    (e : Abelian.Ext.{v} M N n) : e = 0 := by
  rw [← e.mk₀_id_comp, hM.eq_of_src (𝟙 _) 0, Abelian.Ext.mk₀_zero, Abelian.Ext.zero_comp]
end ASGinzburg

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

theorem rightFiniteDimensional_of_isZero {M : A.RightModule} (hM : IsZero M) :
    A.rightFiniteDimensionalProperty M := by
  letI : Subsingleton (A.rightModuleTotalFunctor.obj M) :=
    ModuleCat.isZero_iff_subsingleton.mp (Functor.map_isZero A.rightModuleTotalFunctor hM)
  letI : Module.Finite k (A.rightModuleTotalFunctor.obj M) := inferInstance
  exact Module.Finite.equiv (A.rightModuleTotalFunctorObjIso M).toLinearEquiv

theorem leftFiniteDimensional_of_isZero {M : A.LeftModule} (hM : IsZero M) :
    A.leftFiniteDimensionalProperty M := by
  letI : Subsingleton (A.leftModuleTotalFunctor.obj M) :=
    ModuleCat.isZero_iff_subsingleton.mp (Functor.map_isZero A.leftModuleTotalFunctor hM)
  letI : Module.Finite k (A.leftModuleTotalFunctor.obj M) := inferInstance
  exact Module.Finite.equiv (A.leftModuleTotalFunctorObjIso M).toLinearEquiv

theorem rightModuleExtLeft_isZero_of_isZero {M : A.RightModule} (hM : IsZero M) (n : ℕ) :
    IsZero (A.rightModuleExtLeft M n) := by
  apply A.leftModule_isZero_of_components
  intro i
  apply ModuleCat.isZero_iff_subsingleton.mpr
  exact ⟨fun x y => by rw [ASGinzburg.ext_eq_zero_of_isZero_source hM n x,
    ASGinzburg.ext_eq_zero_of_isZero_source hM n y]⟩

theorem leftModuleExtRight_isZero_of_isZero {M : A.LeftModule} (hM : IsZero M) (n : ℕ) :
    IsZero (A.leftModuleExtRight M n) := by
  rw [IsZero.iff_id_eq_zero]
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  ext e
  exact ASGinzburg.ext_eq_zero_of_isZero_source hM n e
end ASGinzburg.ZAlgebra
