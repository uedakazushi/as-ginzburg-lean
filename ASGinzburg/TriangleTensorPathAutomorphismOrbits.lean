import ASGinzburg.TrianglePathAutomorphismTensorIntertwining
import ASGinzburg.TriangleGLPathAutomorphism
import ASGinzburg.PotentialPathAutomorphismOrbitComparison

/-! Actual triangle tensor orbits and the source's genuine path-algebra
automorphism equivalence of actual potentials are the same relation. -/
namespace ASGinzburg
universe u
variable (k : Type u) [Field k]

theorem triangleTensor_orbit_iff_pathAutomorphism (w w' : CubicTensor333 k) :
    (∃ g : TriangleGL333 k, g • w = w') ↔
      ∃ E : triangle333.VertexCutPathAutomorphism k,
        CutQuiver.VertexCutPathAutomorphism.potentialLinearEquiv triangle333 k E
          (triangleTensorPotentialEquiv k w) = triangleTensorPotentialEquiv k w' := by
  constructor
  · rintro ⟨g,hg⟩
    refine ⟨triangleGLPathAutomorphism k g,?_⟩
    rw [trianglePathAutomorphism_tensorPotential,trianglePathAutomorphismGLTriple_extension]
    change triangleTensorPotentialEquiv k (g • w) = triangleTensorPotentialEquiv k w'
    rw [hg]
  · rintro ⟨E,hE⟩
    refine ⟨trianglePathAutomorphismGLTriple k E,?_⟩
    apply (triangleTensorPotentialEquiv k).injective
    change triangleTensorPotentialEquiv k
      (triangleTensorRepresentation k (trianglePathAutomorphismGLTriple k E) w) =
        triangleTensorPotentialEquiv k w'
    rw [← trianglePathAutomorphism_tensorPotential]
    exact hE

theorem triangleTensorOrbit_eq_iff_potentialPathClass (w w' : CubicTensor333 k) :
    triangleTensorOrbit k w = triangleTensorOrbit k w' ↔
      triangle333.potentialPathAutomorphismClass k (triangleTensorPotentialEquiv k w) =
        triangle333.potentialPathAutomorphismClass k (triangleTensorPotentialEquiv k w') := by
  rw [triangleTensorOrbit_eq_iff,
    triangle333.potentialPathAutomorphismClass_eq_iff_smul]
  exact triangleTensor_orbit_iff_pathAutomorphism k w w'

end ASGinzburg
