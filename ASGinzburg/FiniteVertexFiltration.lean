import ASGinzburg.FiniteDimensionalModules
import ASGinzburg.LeftModuleProjectives
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.Data.Finset.Max

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

theorem rightModule_isZero_of_components (M : A.RightModule)
    (h : ∀ i : ℤ, IsZero ((A.rightModuleEvaluation i).obj M)) : IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  apply NatTrans.ext
  funext X
  exact (h X.unop.index).eq_of_src _ _

theorem rightFiniteDimensional_minimal_nonzero_component {M : A.RightModule}
    (hM : A.rightFiniteDimensionalProperty M) (hn : ¬ IsZero M) :
    ∃ i : ℤ, ¬ IsZero ((A.rightModuleEvaluation i).obj M) ∧
      ∀ j, j < i → IsZero ((A.rightModuleEvaluation j).obj M) := by
  classical
  obtain ⟨S,hS⟩ := A.rightFiniteDimensional_finite_support hM
  let T := S.filter (fun i => ¬ IsZero ((A.rightModuleEvaluation i).obj M))
  have hT : T.Nonempty := by
    by_contra he
    apply hn
    apply A.rightModule_isZero_of_components
    intro i
    by_cases hi : i ∈ S
    · by_contra hnzero
      exact he ⟨i,Finset.mem_filter.mpr ⟨hi,hnzero⟩⟩
    · exact hS i hi
  refine ⟨T.min' hT,(Finset.mem_filter.mp (T.min'_mem hT)).2,?_⟩
  intro j hj
  by_cases hjS : j ∈ S
  · by_contra hnzero
    have hjT : j ∈ T := Finset.mem_filter.mpr ⟨hjS,hnzero⟩
    exact (not_lt_of_ge (T.min'_le j hjT)) hj
  · exact hS j hjS

theorem simpleRightModule_hom_of_low_support {M : A.RightModule} (i : ℤ)
    (hlow : ∀ j, j < i → IsZero ((A.rightModuleEvaluation j).obj M))
    (x : (A.rightModuleEvaluation i).obj M) :
    ∃ f : A.simpleRightModule i ⟶ M,
      A.simpleRightModuleπ i ≫ f = A.representableToElement i M x := by
  let g := A.representableToElement i M x
  have hg : (A.representableRadical i).inclusion ≫ g = 0 := by
    apply NatTrans.ext
    funext Y
    by_cases hy : Y.unop.index < i
    · exact (hlow Y.unop.index hy).eq_of_tgt _ _
    · apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro y
      change g.app Y y.val = 0
      have hy0 : y.val = 0 := by simpa [representableRadical,hy] using y.property
      rw [hy0]
      exact map_zero _
  refine ⟨cokernel.desc _ g hg,?_⟩
  exact cokernel.π_desc _ _ _

theorem rightFiniteDimensional_exists_vertex_simple_subobject {M : A.RightModule}
    (hM : A.rightFiniteDimensionalProperty M) (hn : ¬ IsZero M) :
    ∃ (i : ℤ) (f : A.simpleRightModule i ⟶ M), Mono f ∧ f ≠ 0 := by
  obtain ⟨i,hi,hlow⟩ := A.rightFiniteDimensional_minimal_nonzero_component hM hn
  have hx : ∃ x : (A.rightModuleEvaluation i).obj M, x ≠ 0 := by
    by_contra! hzero
    apply hi
    apply ModuleCat.isZero_iff_subsingleton.mpr
    exact ⟨fun x y => by rw [hzero x,hzero y]⟩
  obtain ⟨x,hx⟩ := hx
  obtain ⟨f,hf⟩ := A.simpleRightModule_hom_of_low_support i hlow x
  have hfn : f ≠ 0 := by
    intro hzero
    rw [hzero,comp_zero] at hf
    apply hx
    have H := congrArg (A.representableYonedaEquiv i M) hf
    change (A.representableYonedaEquiv i M) 0 =
      (A.representableYonedaEquiv i M) ((A.representableYonedaEquiv i M).symm x) at H
    rw [LinearEquiv.apply_symm_apply,map_zero] at H
    exact H.symm
  exact ⟨i,f,mono_of_nonzero_from_simple hfn,hfn⟩
end ASGinzburg.ZAlgebra

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

theorem leftFiniteDimensional_maximal_nonzero_component {M : A.LeftModule}
    (hM : A.leftFiniteDimensionalProperty M) (hn : ¬ IsZero M) :
    ∃ i : ℤ, ¬ IsZero ((A.leftModuleEvaluation i).obj M) ∧
      ∀ j, i < j → IsZero ((A.leftModuleEvaluation j).obj M) := by
  classical
  obtain ⟨S,hS⟩ := A.leftFiniteDimensional_finite_support hM
  let T := S.filter (fun i => ¬ IsZero ((A.leftModuleEvaluation i).obj M))
  have hT : T.Nonempty := by
    by_contra he
    apply hn
    apply A.leftModule_isZero_of_components
    intro i
    by_cases hi : i ∈ S
    · by_contra hnzero
      exact he ⟨i,Finset.mem_filter.mpr ⟨hi,hnzero⟩⟩
    · exact hS i hi
  refine ⟨T.max' hT,(Finset.mem_filter.mp (T.max'_mem hT)).2,?_⟩
  intro j hj
  by_cases hjS : j ∈ S
  · by_contra hnzero
    have hjT : j ∈ T := Finset.mem_filter.mpr ⟨hjS,hnzero⟩
    exact (not_lt_of_ge (T.le_max' j hjT)) hj
  · exact hS j hjS

theorem simpleLeftModule_hom_of_high_support {M : A.LeftModule} (i : ℤ)
    (hhigh : ∀ j, i < j → IsZero ((A.leftModuleEvaluation j).obj M))
    (x : (A.leftModuleEvaluation i).obj M) :
    ∃ f : A.simpleLeftModule i ⟶ M,
      A.simpleLeftModuleπ i ≫ f = A.leftRepresentableToElement i M x := by
  let g := A.leftRepresentableToElement i M x
  have hg : (A.leftRepresentableRadical i).inclusion ≫ g = 0 := by
    apply NatTrans.ext
    funext Y
    by_cases hy : i < Y.index
    · exact (hhigh Y.index hy).eq_of_tgt _ _
    · apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro y
      change g.app Y y.val = 0
      have hy0 : y.val = 0 := by simpa [leftRepresentableRadical,hy] using y.property
      rw [hy0]
      exact map_zero _
  refine ⟨cokernel.desc _ g hg,?_⟩
  exact cokernel.π_desc _ _ _

theorem leftFiniteDimensional_exists_vertex_simple_subobject {M : A.LeftModule}
    (hM : A.leftFiniteDimensionalProperty M) (hn : ¬ IsZero M) :
    ∃ (i : ℤ) (f : A.simpleLeftModule i ⟶ M), Mono f ∧ f ≠ 0 := by
  obtain ⟨i,hi,hhigh⟩ := A.leftFiniteDimensional_maximal_nonzero_component hM hn
  have hx : ∃ x : (A.leftModuleEvaluation i).obj M, x ≠ 0 := by
    by_contra! hzero
    apply hi
    apply ModuleCat.isZero_iff_subsingleton.mpr
    exact ⟨fun x y => by rw [hzero x,hzero y]⟩
  obtain ⟨x,hx⟩ := hx
  obtain ⟨f,hf⟩ := A.simpleLeftModule_hom_of_high_support i hhigh x
  have hfn : f ≠ 0 := by
    intro hzero
    rw [hzero,comp_zero] at hf
    apply hx
    have H := congrArg (A.leftRepresentableYonedaEquiv i M) hf
    change (A.leftRepresentableYonedaEquiv i M) 0 =
      (A.leftRepresentableYonedaEquiv i M) ((A.leftRepresentableYonedaEquiv i M).symm x) at H
    rw [LinearEquiv.apply_symm_apply,map_zero] at H
    exact H.symm
  exact ⟨i,f,mono_of_nonzero_from_simple hfn,hfn⟩
end ASGinzburg.ZAlgebra

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

theorem rightFiniteDimensional_cokernel_finrank_lt {M N : A.RightModule} (f : M ⟶ N)
    (hN : A.rightFiniteDimensionalProperty N) (hf : f ≠ 0) :
    Module.finrank k (A.rightModuleTotalSpace (cokernel f)) < Module.finrank k (A.rightModuleTotalSpace N) := by
  letI : Module.Finite k (A.rightModuleTotalSpace N) := hN
  letI : Module.Finite k (A.rightModuleTotalFunctor.obj N) :=
    Module.Finite.equiv (A.rightModuleTotalFunctorObjIso N).symm.toLinearEquiv
  let g := A.rightModuleTotalFunctor.map f
  have hgn : g.hom ≠ 0 := by
    intro hg
    apply hf
    apply A.rightModuleTotalFunctor.map_injective
    rw [Functor.map_zero]
    exact ModuleCat.hom_ext hg
  have hr : LinearMap.range g.hom ≠ ⊥ := by
    exact fun h => hgn (LinearMap.range_eq_bot.mp h)
  letI : Nontrivial (LinearMap.range g.hom) := Submodule.nontrivial_iff_ne_bot.mpr hr
  have hpos : 0 < Module.finrank k (LinearMap.range g.hom) := Module.finrank_pos
  have hsum := (LinearMap.range g.hom).finrank_quotient_add_finrank
  let e := (A.rightModuleTotalFunctorObjIso (cokernel f)).symm ≪≫
    PreservesCokernel.iso A.rightModuleTotalFunctor f ≪≫ ModuleCat.cokernelIsoRangeQuotient g
  rw [e.toLinearEquiv.finrank_eq,← (A.rightModuleTotalFunctorObjIso N).toLinearEquiv.finrank_eq]
  change Module.finrank k (A.rightModuleTotalFunctor.obj N ⧸ LinearMap.range g.hom) <
    Module.finrank k (A.rightModuleTotalFunctor.obj N)
  omega
end ASGinzburg.ZAlgebra

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

theorem leftFiniteDimensional_cokernel_finrank_lt {M N : A.LeftModule} (f : M ⟶ N)
    (hN : A.leftFiniteDimensionalProperty N) (hf : f ≠ 0) :
    Module.finrank k (A.leftModuleTotalSpace (cokernel f)) < Module.finrank k (A.leftModuleTotalSpace N) := by
  letI : Module.Finite k (A.leftModuleTotalSpace N) := hN
  letI : Module.Finite k (A.leftModuleTotalFunctor.obj N) :=
    Module.Finite.equiv (A.leftModuleTotalFunctorObjIso N).symm.toLinearEquiv
  let g := A.leftModuleTotalFunctor.map f
  have hgn : g.hom ≠ 0 := by
    intro hg
    apply hf
    apply A.leftModuleTotalFunctor.map_injective
    rw [Functor.map_zero]
    exact ModuleCat.hom_ext hg
  have hr : LinearMap.range g.hom ≠ ⊥ := by
    exact fun h => hgn (LinearMap.range_eq_bot.mp h)
  letI : Nontrivial (LinearMap.range g.hom) := Submodule.nontrivial_iff_ne_bot.mpr hr
  have hpos : 0 < Module.finrank k (LinearMap.range g.hom) := Module.finrank_pos
  have hsum := (LinearMap.range g.hom).finrank_quotient_add_finrank
  let e := (A.leftModuleTotalFunctorObjIso (cokernel f)).symm ≪≫
    PreservesCokernel.iso A.leftModuleTotalFunctor f ≪≫ ModuleCat.cokernelIsoRangeQuotient g
  rw [e.toLinearEquiv.finrank_eq,← (A.leftModuleTotalFunctorObjIso N).toLinearEquiv.finrank_eq]
  change Module.finrank k (A.leftModuleTotalFunctor.obj N ⧸ LinearMap.range g.hom) <
    Module.finrank k (A.leftModuleTotalFunctor.obj N)
  omega
end ASGinzburg.ZAlgebra

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

/-- A finite sequence of actual vertex-simple subobjects and cokernel quotients. -/
inductive RightVertexFiltration : A.RightModule → Type (max u (v+1))
  | zero {M} (h : IsZero M) : RightVertexFiltration M
  | step {M} (i : ℤ) (f : A.simpleRightModule i ⟶ M) (hf : Mono f)
      (tail : RightVertexFiltration (cokernel f)) : RightVertexFiltration M

theorem rightFiniteDimensional_hasVertexFiltration (M : A.RightModule)
    (hM : A.rightFiniteDimensionalProperty M) : Nonempty (A.RightVertexFiltration M) := by
  classical
  generalize hn : Module.finrank k (A.rightModuleTotalSpace M) = n
  induction n using Nat.strong_induction_on generalizing M with
  | h n ih =>
    by_cases hz : IsZero M
    · exact ⟨RightVertexFiltration.zero hz⟩
    · obtain ⟨i,f,hf,hfn⟩ := A.rightFiniteDimensional_exists_vertex_simple_subobject hM hz
      letI := hf
      have hq := A.rightFiniteDimensional_of_epi (cokernel.π f) hM
      have hlt : Module.finrank k (A.rightModuleTotalSpace (cokernel f)) < n := by
        rw [← hn]
        exact A.rightFiniteDimensional_cokernel_finrank_lt f hM hfn
      obtain ⟨tail⟩ := ih _ hlt (cokernel f) hq rfl
      exact ⟨RightVertexFiltration.step i f hf tail⟩

noncomputable def rightFiniteDimensionalVertexFiltration (M : A.RightModule)
    (hM : A.rightFiniteDimensionalProperty M) : A.RightVertexFiltration M :=
  (A.rightFiniteDimensional_hasVertexFiltration M hM).some
end ASGinzburg.ZAlgebra

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

/-- A finite sequence of actual vertex-simple subobjects and cokernel quotients. -/
inductive LeftVertexFiltration : A.LeftModule → Type (max u (v+1))
  | zero {M} (h : IsZero M) : LeftVertexFiltration M
  | step {M} (i : ℤ) (f : A.simpleLeftModule i ⟶ M) (hf : Mono f)
      (tail : LeftVertexFiltration (cokernel f)) : LeftVertexFiltration M

theorem leftFiniteDimensional_hasVertexFiltration (M : A.LeftModule)
    (hM : A.leftFiniteDimensionalProperty M) : Nonempty (A.LeftVertexFiltration M) := by
  classical
  generalize hn : Module.finrank k (A.leftModuleTotalSpace M) = n
  induction n using Nat.strong_induction_on generalizing M with
  | h n ih =>
    by_cases hz : IsZero M
    · exact ⟨LeftVertexFiltration.zero hz⟩
    · obtain ⟨i,f,hf,hfn⟩ := A.leftFiniteDimensional_exists_vertex_simple_subobject hM hz
      letI := hf
      have hq := A.leftFiniteDimensional_of_epi (cokernel.π f) hM
      have hlt : Module.finrank k (A.leftModuleTotalSpace (cokernel f)) < n := by
        rw [← hn]
        exact A.leftFiniteDimensional_cokernel_finrank_lt f hM hfn
      obtain ⟨tail⟩ := ih _ hlt (cokernel f) hq rfl
      exact ⟨LeftVertexFiltration.step i f hf tail⟩

noncomputable def leftFiniteDimensionalVertexFiltration (M : A.LeftModule)
    (hM : A.leftFiniteDimensionalProperty M) : A.LeftVertexFiltration M :=
  (A.leftFiniteDimensional_hasVertexFiltration M hM).some
end ASGinzburg.ZAlgebra
