import ASGinzburg.FoundationComponentSumModuleIso

/-! The actual finite component sum is natural in ring-module maps,
giving the counit isomorphism for total space and component recovery. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory
open scoped ModuleCat.Algebra
attribute [local instance 2000] ModuleCat.isModule
universe u
variable {k : Type u} [Field k] (A : ZAlgebra.{u,u} k) (Q : CutQuiver)

theorem foundationRingRightComponentSumModuleMap_natural
    {M N : ModuleCat.{u} (A.FoundationAlgebra Q)ᵐᵒᵖ} (f : M ⟶ N) :
    (A.foundationRightTotalFunctor Q).map ((A.foundationRingRightComponentRecovery Q).map f) ≫
      A.foundationRingRightComponentSumModuleMap Q N=
      A.foundationRingRightComponentSumModuleMap Q M ≫ f := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (∑ i : Q.Vertex,f.hom (x i).val)=f.hom (∑ i : Q.Vertex,(x i).val)
  exact (map_sum f.hom (fun i : Q.Vertex => (x i).val) Finset.univ).symm

noncomputable def foundationRingRightCounitIso :
    A.foundationRingRightComponentRecovery Q ⋙ A.foundationRightTotalFunctor Q ≅
      𝟭 (ModuleCat.{u} (A.FoundationAlgebra Q)ᵐᵒᵖ) :=
  NatIso.ofComponents (A.foundationRingRightComponentSumModuleIso Q)
    (fun f => A.foundationRingRightComponentSumModuleMap_natural Q f)

end ASGinzburg.ZAlgebra
