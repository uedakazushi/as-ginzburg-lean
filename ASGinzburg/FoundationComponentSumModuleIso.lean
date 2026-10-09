import ASGinzburg.FoundationComponentSumActions
import ASGinzburg.FiniteComponentDecomposition

/-! The component sum preserves the actual whole-ring action and
is an isomorphism of genuine foundation-ring modules. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory
open scoped ModuleCat.Algebra
attribute [local instance 2000] ModuleCat.isModule
universe u
variable {k : Type u} [Field k] (A : ZAlgebra.{u,u} k) (Q : CutQuiver)

theorem foundationRingRightComponentSum_representation
    (M : ModuleCat.{u} (A.FoundationAlgebra Q)ᵐᵒᵖ) (a : A.FoundationAlgebra Q)
    (x : A.foundationRightTotalSpace Q (A.foundationRingRightComponentModule Q M)) :
    A.foundationRingRightComponentSum Q M
      (A.foundationRightTotalAction Q (A.foundationRingRightComponentModule Q M) a x)=
      MulOpposite.op a • A.foundationRingRightComponentSum Q M x := by
  classical
  have he := congrArg (fun b : A.FoundationAlgebra Q =>
    A.foundationRightTotalRepresentation Q (A.foundationRingRightComponentModule Q M) b)
    ((A.foundationComponents Q).sum_totalComponent a)
  simp only [map_sum] at he
  have hop := congrArg (fun b : A.FoundationAlgebra Q => MulOpposite.opAddEquiv b)
    ((A.foundationComponents Q).sum_totalComponent a)
  simp only [map_sum] at hop
  change (∑ i : Q.Vertex,∑ j : Q.Vertex,
    MulOpposite.op ((A.foundationComponents Q).totalComponent i j (a i j)))=
    MulOpposite.op a at hop
  change (∑ i : Q.Vertex,∑ j : Q.Vertex,
    A.foundationRightTotalAction Q (A.foundationRingRightComponentModule Q M)
      ((A.foundationComponents Q).totalComponent i j (a i j)))=
    A.foundationRightTotalAction Q (A.foundationRingRightComponentModule Q M) a at he
  rw [←he,←hop]
  simp only [LinearMap.sum_apply,map_sum,Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact A.foundationRingRightComponentSum_action Q M (a i j) x

noncomputable def foundationRingRightComponentSumModuleMap
    (M : ModuleCat.{u} (A.FoundationAlgebra Q)ᵐᵒᵖ) :
    A.foundationRightTotalModule Q (A.foundationRingRightComponentModule Q M) ⟶ M := by
  letI := A.foundationRightTotalModuleStructure Q (A.foundationRingRightComponentModule Q M)
  exact ModuleCat.ofHom
    { toFun := fun x => A.foundationRingRightComponentSum Q M x
      map_add' := (A.foundationRingRightComponentSum Q M).map_add
      map_smul' := by
        intro r x
        change A.foundationRingRightComponentSum Q M
          (A.foundationRightTotalAction Q (A.foundationRingRightComponentModule Q M) r.unop x)=_
        exact A.foundationRingRightComponentSum_representation Q M r.unop x }

noncomputable def foundationRingRightComponentSumModuleIso
    (M : ModuleCat.{u} (A.FoundationAlgebra Q)ᵐᵒᵖ) :
    A.foundationRightTotalModule Q (A.foundationRingRightComponentModule Q M) ≅ M :=
  (LinearEquiv.ofBijective (A.foundationRingRightComponentSumModuleMap Q M).hom
    (by
      change Function.Bijective (A.foundationRingRightComponentSum Q M)
      exact (A.foundationRingRightComponentSumEquiv Q M).bijective)).toModuleIso

end ASGinzburg.ZAlgebra
