import ASGinzburg.ZAlgebraIsomorphisms

/-! The actual opposite directed Z-algebra with reflected integer indices.
All local finiteness, positivity and connectedness fields are proved. -/
namespace ASGinzburg.ZAlgebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

def reflected (c : ℤ) : ZAlgebra.{u,v} k where
  Hom i j := A.Hom (c-j) (c-i)
  id i := A.id (c-i)
  comp := LinearMap.flip A.comp
  comp_id f := A.id_comp f
  id_comp f := A.comp_id f
  comp_assoc f g h := (A.comp_assoc h g f).symm
  positive := by
    intro i j hij f
    exact A.positive (by omega) f
  connected i f := A.connected (c-i) f
  id_nonzero i := A.id_nonzero (c-i)
  finite i j := A.finite (c-j) (c-i)

@[simp] theorem reflected_comp (c : ℤ) {i j l : ℤ}
    (f : (A.reflected c).Hom i j) (g : (A.reflected c).Hom j l) :
    (A.reflected c).comp g f = A.comp f g := rfl

end ASGinzburg.ZAlgebra
