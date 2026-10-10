import ASGinzburg.TrianglePotentialCoordinates

/-! The actual closed-path potential space in Corollary 5.2 has dimension
27, by the proved tensor identification. -/
namespace ASGinzburg
universe u
variable (k : Type u) [Field k]

noncomputable instance trianglePotentialFinite : Module.Finite k (triangle333.Potential k) :=
  Module.Finite.equiv (triangleTensorPotentialEquiv k)

theorem trianglePotential_finrank : Module.finrank k (triangle333.Potential k) = 27 := by
  rw [← (triangleTensorPotentialEquiv k).finrank_eq]
  exact cubicTensor333_finrank k

end ASGinzburg
