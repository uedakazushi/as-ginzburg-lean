import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-! Genuine injective linear parametrizations of one subspace give an
actual invertible change of basis and its commuting identity. -/
namespace ASGinzburg
universe u v w
variable {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]
  {M : Type w} [AddCommGroup M] [Module k M]

noncomputable def linearMapSameRangeBasisChange (f g : V →ₗ[k] M)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (h : LinearMap.range f = LinearMap.range g) : V ≃ₗ[k] V :=
  (LinearEquiv.ofInjective g hg).trans
    ((LinearEquiv.ofEq (LinearMap.range g) (LinearMap.range f) h.symm).trans
      (LinearEquiv.ofInjective f hf).symm)

theorem linearMapSameRangeBasisChange_commutes (f g : V →ₗ[k] M)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (h : LinearMap.range f = LinearMap.range g) (x : V) :
    f (linearMapSameRangeBasisChange f g hf hg h x) = g x := by
  let e := LinearEquiv.ofInjective f hf
  let y : LinearMap.range f :=
    LinearEquiv.ofEq (LinearMap.range g) (LinearMap.range f) h.symm
      (LinearEquiv.ofInjective g hg x)
  exact congrArg Subtype.val (e.apply_symm_apply y)

end ASGinzburg
