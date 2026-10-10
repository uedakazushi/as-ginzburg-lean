import ASGinzburg.ZAlgebraHomomorphisms

namespace ASGinzburg.ZAlgebra.LinearIdeal
universe u v
variable {k : Type u} [Field k] {B : ZAlgebra.{u,v} k}

theorem eq_of_hom_eq (I J : B.LinearIdeal) (h : ∀ i j, I.hom i j = J.hom i j) : I = J := by
  cases I
  cases J
  congr
  exact funext fun i => funext fun j => h i j

end ASGinzburg.ZAlgebra.LinearIdeal
