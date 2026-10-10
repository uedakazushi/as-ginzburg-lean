import work.ASGinzburgDraft.TriangleASFoundationPotentialIsomorphismOrbits
import work.ASGinzburgDraft.TriangleGinzburgFoundationPotentialOrbit
import work.ASGinzburgDraft.TriangleASGinzburgClassInjection

/-! The literal AS foundation tensor defines an unconditional map on
actual quadratic AS isomorphism classes to actual tensor GL orbits.
On original Ginzburg-regular source tensors its composite is the original
tensor orbit. This does not assert candidate regularity for all AS algebras. -/
namespace ASGinzburg
universe u
variable (k : Type u) [Field k]

noncomputable def QuadraticASAlgebra.foundationTensor333
    (A : QuadraticASAlgebra.{u,u} k) : CubicTensor333 k :=
  ((A.val.quadraticASRegular_iff_triangleASRegular).mp A.property).triangleFoundationTensor A.val

noncomputable def quadraticASFoundationTensorOrbitMap :
    QuadraticASIsomorphismClass.{u,u} k → TriangleTensorOrbit k :=
  Quotient.lift (fun A : QuadraticASAlgebra.{u,u} k =>
    triangleTensorOrbit k (A.foundationTensor333 k)) (by
      intro A B h
      obtain ⟨F⟩ := h
      apply (triangleTensorOrbit_eq_iff k _ _).mpr
      exact triangleASRegular_Isomorphism_foundationTensor_orbit k A.val B.val F
        ((A.val.quadraticASRegular_iff_triangleASRegular).mp A.property)
        ((B.val.quadraticASRegular_iff_triangleASRegular).mp B.property))

theorem quadraticASFoundationTensorOrbitMap_apply (A : QuadraticASAlgebra.{u,u} k) :
    quadraticASFoundationTensorOrbitMap k (A.isomorphismClass k) =
      triangleTensorOrbit k (A.foundationTensor333 k) := rfl

theorem quadraticASFoundationTensorOrbitMap_regularTensor
    (w : GinzburgRegularTensor333 k) :
    quadraticASFoundationTensorOrbitMap k (w.asQuadraticASClass k) =
      triangleTensorOrbit k w.val := by
  change triangleTensorOrbit k ((w.asQuadraticASAlgebra k).foundationTensor333 k) = _
  apply (triangleTensorOrbit_eq_iff k _ _).mpr
  have h := triangleGinzburgRegular_foundationTensor_GL_orbit k
    (triangleTensorPotentialEquiv k w.val) w.property
  simpa only [LinearEquiv.symm_apply_apply] using h

noncomputable def regularTensorForgetOrbit333 :
    GinzburgRegularTensorOrbit333 k → TriangleTensorOrbit k :=
  Quotient.lift (fun w : GinzburgRegularTensor333 k => triangleTensorOrbit k w.val)
    (by intro w w' h; exact Quotient.sound h)

theorem regularTensorForgetOrbit333_apply (w : GinzburgRegularTensor333 k) :
    regularTensorForgetOrbit333 k (w.orbitClass k) = triangleTensorOrbit k w.val := rfl

theorem regularTensorForgetOrbit333_injective :
    Function.Injective (regularTensorForgetOrbit333 k) := by
  intro C D
  refine Quotient.inductionOn₂ C D ?_
  intro w w' h
  have h' : triangleTensorOrbit k w.val = triangleTensorOrbit k w'.val := h
  exact (GinzburgRegularTensor333.orbitClass_eq_iff k w w').mpr
    ((triangleTensorOrbit_eq_iff k w.val w'.val).mp h')

theorem quadraticASFoundationTensorOrbitMap_source_composition
    (C : GinzburgRegularTensorOrbit333 k) :
    quadraticASFoundationTensorOrbitMap k (corollary52ClassMap k (corollary52Class k) C) =
      regularTensorForgetOrbit333 k C := by
  refine Quotient.inductionOn C ?_
  intro w
  exact quadraticASFoundationTensorOrbitMap_regularTensor k w

end ASGinzburg
