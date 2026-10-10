import work.ASGinzburgDraft.Corollary52CorrespondenceReduction

/-! Genuine equivalences of the actual tensor and potential orbit spaces,
independent of the outstanding AS/Ginzburg correspondence. -/
namespace ASGinzburg
universe u
variable (k : Type u) [Field k]

noncomputable def triangleTensorPotentialOrbitEquiv :
    TriangleTensorOrbit k ≃ triangle333.PotentialPathAutomorphismClass k :=
  Quotient.congr (triangleTensorPotentialEquiv k).toEquiv (fun w w' => by
    have h := triangleTensorOrbit_eq_iff_potentialPathClass k w w'
    simpa only [triangleTensorOrbit, CutQuiver.potentialPathAutomorphismClass,
      Quotient.eq] using h)

theorem triangleTensorPotentialOrbitEquiv_apply (w : CubicTensor333 k) :
    triangleTensorPotentialOrbitEquiv k (triangleTensorOrbit k w) =
      triangle333.potentialPathAutomorphismClass k (triangleTensorPotentialEquiv k w) := rfl

noncomputable def triangleRegularTensorPotentialOrbitEquiv :
    GinzburgRegularTensorOrbit333 k ≃
      GinzburgRegularPotentialPathAutomorphismClass k triangle333 :=
  Quotient.congr (ginzburgRegularTensorPotentialEquiv333 k) (fun w w' => by
    have h := regularTensorOrbitClass_eq_iff_potentialPathClass k w w'
    simpa only [GinzburgRegularTensor333.orbitClass,
      GinzburgRegularPotential.pathAutomorphismClass, Quotient.eq] using h)

theorem triangleRegularTensorPotentialOrbitEquiv_apply (w : GinzburgRegularTensor333 k) :
    triangleRegularTensorPotentialOrbitEquiv k (w.orbitClass k) =
      (ginzburgRegularTensorPotentialEquiv333 k w).pathAutomorphismClass k triangle333 := rfl

end ASGinzburg
