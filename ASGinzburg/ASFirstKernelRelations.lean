import ASGinzburg.ASRelationGeneratorBasis

/-! Replace the kernel of the epimorphic AS first cover by the actual
kernel of d₁, preserving its genuine positive-action top and cut-arrow
basis. The comparison with the free-path minimal relation quotient is
not part of this result. -/
namespace ASGinzburg.ZAlgebra.ASResolution
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k} {Q : CutQuiver}
  {w : Q.LiftVertex} (R : A.ASResolution Q w)

noncomputable def firstCoverKernelD₁Iso : kernel R.firstCover ≅ kernel R.d₁ :=
  (kernelCompMono R.firstCover (kernel.ι (A.simpleRightModuleπ (Q.height w)))).symm ≪≫
    kernel.congr _ _ R.firstCover_ι

noncomputable def firstCoverKernelTopEquiv (i : ℤ) :
    ((A.rightModuleEvaluation i).obj (kernel R.firstCover) ⧸
      A.positiveActionSpan (kernel R.firstCover) i) ≃ₗ[k]
      ((A.rightModuleEvaluation i).obj (kernel R.d₁) ⧸
        A.positiveActionSpan (kernel R.d₁) i) :=
  Submodule.Quotient.equiv _ _
    ((A.rightModuleEvaluation i).mapIso R.firstCoverKernelD₁Iso).toLinearEquiv
      (A.positiveActionSpan_map_of_epi R.firstCoverKernelD₁Iso.hom i)

noncomputable def foundationFirstKernelRelationBasis {j : Q.Vertex}
    (R : A.ASResolution Q (j,0)) (i : Q.Vertex) :
    Module.Basis (Q.FoundationRelationArrow i j) k
      ((A.rightModuleEvaluation (i.val : ℤ)).obj (kernel R.d₁) ⧸
        A.positiveActionSpan (kernel R.d₁) (i.val : ℤ)) :=
  (R.foundationRelationTopBasis i j).map (R.firstCoverKernelTopEquiv (i.val : ℤ))

end ASGinzburg.ZAlgebra.ASResolution
