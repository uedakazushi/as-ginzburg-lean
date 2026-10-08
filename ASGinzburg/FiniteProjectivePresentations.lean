import ASGinzburg.FiniteProjectiveClosure
import ASGinzburg.FiniteDimensionalModules
import ASGinzburg.LeftModuleProjectives

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

theorem rightFiniteDimensional_component_finite {M : A.RightModule}
    (hM : A.rightFiniteDimensionalProperty M) (i : ℤ) :
    Module.Finite k ((A.rightModuleEvaluation i).obj M) := by
  classical
  letI : Module.Finite k (A.rightModuleTotalSpace M) := hM
  apply FiniteDimensional.of_injective
    (DirectSum.lof k ℤ (fun j => (A.rightModuleEvaluation j).obj M) i)
  intro x y h
  have H := congrArg (DirectSum.component k ℤ (fun j => (A.rightModuleEvaluation j).obj M) i) h
  simpa only [DirectSum.component.lof_self] using H

noncomputable def finiteRightModuleSupport (M : A.RightModule)
    (hM : A.rightFiniteDimensionalProperty M) : Finset ℤ :=
  (A.rightFiniteDimensional_finite_support hM).choose

theorem finiteRightModuleSupport_isZero (M : A.RightModule)
    (hM : A.rightFiniteDimensionalProperty M) (i : ℤ) (hi : i ∉ A.finiteRightModuleSupport M hM) :
    IsZero ((A.rightModuleEvaluation i).obj M) :=
  (A.rightFiniteDimensional_finite_support hM).choose_spec i hi

noncomputable def finiteRightModuleComponentBasis (M : A.RightModule)
    (hM : A.rightFiniteDimensionalProperty M) (i : ℤ) :
    Module.Basis (Fin (Module.finrank k ((A.rightModuleEvaluation i).obj M))) k
      ((A.rightModuleEvaluation i).obj M) := by
  letI := A.rightFiniteDimensional_component_finite hM i
  exact Module.finBasis k _

def finiteRightModuleGeneratorIndex (M : A.RightModule)
    (hM : A.rightFiniteDimensionalProperty M) :=
  Σ i : A.finiteRightModuleSupport M hM, Fin (Module.finrank k ((A.rightModuleEvaluation i).obj M))

noncomputable instance finiteRightModuleGeneratorIndexFintype (M : A.RightModule)
    (hM : A.rightFiniteDimensionalProperty M) : Fintype (A.finiteRightModuleGeneratorIndex M hM) :=
  inferInstanceAs (Fintype (Σ i : A.finiteRightModuleSupport M hM,
    Fin (Module.finrank k ((A.rightModuleEvaluation i).obj M))))

noncomputable def finiteFreeRightModule (M : A.RightModule)
    (hM : A.rightFiniteDimensionalProperty M) : A.RightModule :=
  ∐ fun g : A.finiteRightModuleGeneratorIndex M hM => A.representable g.1

noncomputable def finiteFreeRightModuleπ (M : A.RightModule)
    (hM : A.rightFiniteDimensionalProperty M) : A.finiteFreeRightModule M hM ⟶ M :=
  Sigma.desc fun g : A.finiteRightModuleGeneratorIndex M hM =>
    (A.representableYonedaEquiv g.1 M).symm (A.finiteRightModuleComponentBasis M hM g.1 g.2)

theorem finiteFreeRightModule_finiteProjective (M : A.RightModule)
    (hM : A.rightFiniteDimensionalProperty M) :
    A.rightFiniteProjectiveProperty (A.finiteFreeRightModule M hM) :=
  A.rightFiniteProjectiveProperty_coproduct (fun g : A.finiteRightModuleGeneratorIndex M hM => g.1)

noncomputable instance finiteFreeRightModuleProjective (M : A.RightModule)
    (hM : A.rightFiniteDimensionalProperty M) : Projective (A.finiteFreeRightModule M hM) :=
  A.rightFiniteProjectiveProperty_projective (A.finiteFreeRightModule_finiteProjective M hM)

noncomputable instance finiteFreeRightModuleπEpi (M : A.RightModule)
    (hM : A.rightFiniteDimensionalProperty M) : Epi (A.finiteFreeRightModuleπ M hM) := by
  classical
  apply (A.rightModule_epi_iff_surjective _).mpr
  intro i x
  by_cases hi : i ∈ A.finiteRightModuleSupport M hM
  · let b := A.finiteRightModuleComponentBasis M hM i
    let y := fun j : Fin (Module.finrank k ((A.rightModuleEvaluation i).obj M)) =>
      (A.rightModuleEvaluation i).map
        (Sigma.ι (fun g : A.finiteRightModuleGeneratorIndex M hM => A.representable g.1)
          (⟨⟨i,hi⟩,j⟩ : A.finiteRightModuleGeneratorIndex M hM)) (A.id i)
    refine ⟨∑ j, (b.repr x j) • y j,?_⟩
    have H : ∀ j, (A.rightModuleEvaluation i).map (A.finiteFreeRightModuleπ M hM) (y j) = b j := by
      intro j
      let g : A.finiteRightModuleGeneratorIndex M hM := ⟨⟨i,hi⟩,j⟩
      have h := Sigma.ι_desc (fun g : A.finiteRightModuleGeneratorIndex M hM =>
        (A.representableYonedaEquiv g.1 M).symm (A.finiteRightModuleComponentBasis M hM g.1 g.2)) g
      have h' := congrArg (A.representableYonedaEquiv i M) h
      rw [A.representableYonedaEquiv_comp,LinearEquiv.apply_symm_apply] at h'
      exact h'
    simp only [map_sum,map_smul,H]
    exact b.sum_repr x
  · have hx : x = 0 := (ModuleCat.isZero_iff_subsingleton.mp
      (A.finiteRightModuleSupport_isZero M hM i hi)).elim _ _
    exact ⟨0,by simpa only [map_zero] using hx.symm⟩
end ASGinzburg.ZAlgebra

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

theorem leftFiniteDimensional_component_finite {M : A.LeftModule}
    (hM : A.leftFiniteDimensionalProperty M) (i : ℤ) :
    Module.Finite k ((A.leftModuleEvaluation i).obj M) := by
  classical
  letI : Module.Finite k (A.leftModuleTotalSpace M) := hM
  apply FiniteDimensional.of_injective
    (DirectSum.lof k ℤ (fun j => (A.leftModuleEvaluation j).obj M) i)
  intro x y h
  have H := congrArg (DirectSum.component k ℤ (fun j => (A.leftModuleEvaluation j).obj M) i) h
  simpa only [DirectSum.component.lof_self] using H

noncomputable def finiteLeftModuleSupport (M : A.LeftModule)
    (hM : A.leftFiniteDimensionalProperty M) : Finset ℤ :=
  (A.leftFiniteDimensional_finite_support hM).choose

theorem finiteLeftModuleSupport_isZero (M : A.LeftModule)
    (hM : A.leftFiniteDimensionalProperty M) (i : ℤ) (hi : i ∉ A.finiteLeftModuleSupport M hM) :
    IsZero ((A.leftModuleEvaluation i).obj M) :=
  (A.leftFiniteDimensional_finite_support hM).choose_spec i hi

noncomputable def finiteLeftModuleComponentBasis (M : A.LeftModule)
    (hM : A.leftFiniteDimensionalProperty M) (i : ℤ) :
    Module.Basis (Fin (Module.finrank k ((A.leftModuleEvaluation i).obj M))) k
      ((A.leftModuleEvaluation i).obj M) := by
  letI := A.leftFiniteDimensional_component_finite hM i
  exact Module.finBasis k _

def finiteLeftModuleGeneratorIndex (M : A.LeftModule)
    (hM : A.leftFiniteDimensionalProperty M) :=
  Σ i : A.finiteLeftModuleSupport M hM, Fin (Module.finrank k ((A.leftModuleEvaluation i).obj M))

noncomputable instance finiteLeftModuleGeneratorIndexFintype (M : A.LeftModule)
    (hM : A.leftFiniteDimensionalProperty M) : Fintype (A.finiteLeftModuleGeneratorIndex M hM) :=
  inferInstanceAs (Fintype (Σ i : A.finiteLeftModuleSupport M hM,
    Fin (Module.finrank k ((A.leftModuleEvaluation i).obj M))))

noncomputable def finiteFreeLeftModule (M : A.LeftModule)
    (hM : A.leftFiniteDimensionalProperty M) : A.LeftModule :=
  ∐ fun g : A.finiteLeftModuleGeneratorIndex M hM => A.leftRepresentable g.1

noncomputable def finiteFreeLeftModuleπ (M : A.LeftModule)
    (hM : A.leftFiniteDimensionalProperty M) : A.finiteFreeLeftModule M hM ⟶ M :=
  Sigma.desc fun g : A.finiteLeftModuleGeneratorIndex M hM =>
    (A.leftRepresentableYonedaEquiv g.1 M).symm (A.finiteLeftModuleComponentBasis M hM g.1 g.2)

theorem finiteFreeLeftModule_finiteProjective (M : A.LeftModule)
    (hM : A.leftFiniteDimensionalProperty M) :
    A.leftFiniteProjectiveProperty (A.finiteFreeLeftModule M hM) :=
  A.leftFiniteProjectiveProperty_coproduct (fun g : A.finiteLeftModuleGeneratorIndex M hM => g.1)

noncomputable instance finiteFreeLeftModuleProjective (M : A.LeftModule)
    (hM : A.leftFiniteDimensionalProperty M) : Projective (A.finiteFreeLeftModule M hM) :=
  A.leftFiniteProjectiveProperty_projective (A.finiteFreeLeftModule_finiteProjective M hM)

noncomputable instance finiteFreeLeftModuleπEpi (M : A.LeftModule)
    (hM : A.leftFiniteDimensionalProperty M) : Epi (A.finiteFreeLeftModuleπ M hM) := by
  classical
  apply (A.leftModule_epi_iff_surjective _).mpr
  intro i x
  by_cases hi : i ∈ A.finiteLeftModuleSupport M hM
  · let b := A.finiteLeftModuleComponentBasis M hM i
    let y := fun j : Fin (Module.finrank k ((A.leftModuleEvaluation i).obj M)) =>
      (A.leftModuleEvaluation i).map
        (Sigma.ι (fun g : A.finiteLeftModuleGeneratorIndex M hM => A.leftRepresentable g.1)
          (⟨⟨i,hi⟩,j⟩ : A.finiteLeftModuleGeneratorIndex M hM)) (A.id i)
    refine ⟨∑ j, (b.repr x j) • y j,?_⟩
    have H : ∀ j, (A.leftModuleEvaluation i).map (A.finiteFreeLeftModuleπ M hM) (y j) = b j := by
      intro j
      let g : A.finiteLeftModuleGeneratorIndex M hM := ⟨⟨i,hi⟩,j⟩
      have h := Sigma.ι_desc (fun g : A.finiteLeftModuleGeneratorIndex M hM =>
        (A.leftRepresentableYonedaEquiv g.1 M).symm (A.finiteLeftModuleComponentBasis M hM g.1 g.2)) g
      have h' := congrArg (A.leftRepresentableYonedaEquiv i M) h
      rw [A.leftRepresentableYonedaEquiv_comp,LinearEquiv.apply_symm_apply] at h'
      exact h'
    simp only [map_sum,map_smul,H]
    exact b.sum_repr x
  · have hx : x = 0 := (ModuleCat.isZero_iff_subsingleton.mp
      (A.finiteLeftModuleSupport_isZero M hM i hi)).elim _ _
    exact ⟨0,by simpa only [map_zero] using hx.symm⟩
end ASGinzburg.ZAlgebra
