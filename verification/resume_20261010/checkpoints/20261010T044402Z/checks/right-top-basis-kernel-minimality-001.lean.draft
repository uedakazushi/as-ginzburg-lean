import work.ASGinzburgDraft.RightTopBasisCoordinates
import ASGinzburg.RightModuleMinimality

/-! The actual kernel of the basis-of-top presentation lies in its
projective source's positive radical. The diagonal coefficients vanish
by the chosen top basis; every off-diagonal component is radical. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
open scoped DirectSum
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

theorem rightTopBasisFreeModuleπ_mem_radical_of_map_eq_zero
    (M : A.RightModule) (i : ℤ)
    (x : (A.rightModuleEvaluation i).obj (A.rightTopBasisFreeModule M))
    (hx : (A.rightModuleEvaluation i).map (A.rightTopBasisFreeModuleπ M) x = 0) :
    x ∈ A.positiveActionSpan (A.rightTopBasisFreeModule M) i := by
  classical
  apply (A.rightSmallCoproduct_radical_iff
    (fun g : A.rightTopBasisIndex M => A.representable g.1) i x).mpr
  rintro ⟨l, j⟩
  by_cases hl : l = i
  · subst l
    have hcoord := A.rightTopBasisFreeModuleπ_coordinate M i j x
    have hz : (A.scalarEndEquiv i).symm
        ((A.rightSmallCoproductComponentIso
          (fun g : A.rightTopBasisIndex M => A.representable g.1) i).hom.hom x ⟨i,j⟩) = 0 := by
      simpa only [hx, map_zero, Finsupp.zero_apply] using hcoord.symm
    have hz' := (A.scalarEndEquiv i).symm.injective
      (show (A.scalarEndEquiv i).symm
          ((A.rightSmallCoproductComponentIso
            (fun g : A.rightTopBasisIndex M => A.representable g.1) i).hom.hom x ⟨i,j⟩) =
        (A.scalarEndEquiv i).symm 0 from by simpa only [map_zero] using hz)
    rw [hz']
    exact Submodule.zero_mem _
  · exact A.representable_component_mem_radical_of_ne i l hl _

theorem rightTopBasisFreeModuleπ_kernel_inclusion_minimal (M : A.RightModule) :
    A.IsMinimalMorphism (kernel.ι (A.rightTopBasisFreeModuleπ M)) := by
  intro i y
  apply A.rightTopBasisFreeModuleπ_mem_radical_of_map_eq_zero M i
  have hzero := congrArg
    (fun f => ((A.rightModuleEvaluation i).map f).hom y)
    (kernel.condition (A.rightTopBasisFreeModuleπ M))
  simpa only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply,
    Functor.map_zero, ModuleCat.hom_zero, LinearMap.zero_apply] using hzero

end ASGinzburg.ZAlgebra
