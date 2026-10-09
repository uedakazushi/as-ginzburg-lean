import ASGinzburg.Representables

/-! The connected endomorphism components have the genuine scalar
multiplication, and their scalar-coordinate inverse preserves it. -/
namespace ASGinzburg.ZAlgebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

theorem scalarEndEquiv_apply (i : ℤ) (c : k) : A.scalarEndEquiv i c=c • A.id i := by
  simp only [scalarEndEquiv,LinearEquiv.ofBijective_apply,LinearMap.toSpanSingleton_apply]

theorem scalarEndEquiv_symm_id (i : ℤ) : (A.scalarEndEquiv i).symm (A.id i)=1 := by
  have h1 : A.scalarEndEquiv i 1=A.id i := by rw [A.scalarEndEquiv_apply,one_smul]
  rw [← h1,LinearEquiv.symm_apply_apply]

theorem scalarEndEquiv_mul (i : ℤ) (c d : k) :
    A.scalarEndEquiv i (c*d)=A.comp (A.scalarEndEquiv i c) (A.scalarEndEquiv i d) := by
  rw [A.scalarEndEquiv_apply,A.scalarEndEquiv_apply,A.scalarEndEquiv_apply,
    A.comp.map_smul,LinearMap.smul_apply,map_smul,A.comp_id,smul_smul]

theorem scalarEndEquiv_symm_comp (i : ℤ) (f g : A.Hom i i) :
    (A.scalarEndEquiv i).symm (A.comp g f)=
      (A.scalarEndEquiv i).symm g*(A.scalarEndEquiv i).symm f := by
  apply (A.scalarEndEquiv i).injective
  rw [LinearEquiv.apply_symm_apply,A.scalarEndEquiv_mul,
    LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]

end ASGinzburg.ZAlgebra
