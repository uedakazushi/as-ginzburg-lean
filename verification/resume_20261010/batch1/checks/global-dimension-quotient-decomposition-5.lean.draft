import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Algebra.Opposite
import Mathlib.Algebra.Algebra.Pi
import Mathlib.RingTheory.Finiteness.Basic

/-! The actual quotient by the kernel of a scalar augmentation is the
finite sum of its genuine coordinate modules. The coordinate modules
may live in a different universe from the scalar field. -/
namespace ASGinzburg
open CategoryTheory
universe u v w z
variable {k : Type u} [Field k] {R : Type w} [Ring R] [Algebra k R]
variable {I : Type z} (f : R →ₐ[k] (I → k))

noncomputable instance idealQuotientRightModule (J : Ideal R) [J.IsTwoSided] :
    Module Rᵐᵒᵖ (R ⧸ J)ᵐᵒᵖ :=
  Module.compHom _ (Ideal.Quotient.mk J).op

noncomputable def idealQuotientRightObject (J : Ideal R) [J.IsTwoSided] :
    ModuleCat.{w} Rᵐᵒᵖ := ModuleCat.of _ (R ⧸ J)ᵐᵒᵖ

noncomputable def idealQuotientRightProjection (J : Ideal R) [J.IsTwoSided] :
    Rᵐᵒᵖ →ₗ[Rᵐᵒᵖ] (R ⧸ J)ᵐᵒᵖ where
  toFun := (Ideal.Quotient.mk J).op
  map_add' := map_add _
  map_smul' := map_mul _

theorem idealQuotientRightProjection_surjective (J : Ideal R) [J.IsTwoSided] :
    Function.Surjective (idealQuotientRightProjection J) := by
  intro s
  obtain ⟨r,hr⟩ := Ideal.Quotient.mk_surjective s.unop
  refine ⟨MulOpposite.op r, ?_⟩
  exact congrArg MulOpposite.op hr

instance idealQuotientRight_finite (J : Ideal R) [J.IsTwoSided] :
    Module.Finite Rᵐᵒᵖ (R ⧸ J)ᵐᵒᵖ :=
  Module.Finite.of_surjective (idealQuotientRightProjection J)
    (idealQuotientRightProjection_surjective J)

noncomputable def idealQuotientRightLinearEquivOfEq
    (J K : Ideal R) [J.IsTwoSided] [K.IsTwoSided] (h : J=K) :
    (R ⧸ J)ᵐᵒᵖ ≃ₗ[Rᵐᵒᵖ] (R ⧸ K)ᵐᵒᵖ := by
  subst K
  exact LinearEquiv.refl _ _

noncomputable def scalarQuotientRightObject : ModuleCat.{w} Rᵐᵒᵖ :=
  idealQuotientRightObject (RingHom.ker f.toRingHom)

noncomputable def scalarQuotientVertexLinearEquiv
    (hf : Function.Surjective f) (V : I → ModuleCat.{v} Rᵐᵒᵖ)
    [∀ i, Module k (V i)] (e : ∀ i, V i ≃ₗ[k] k)
    (hscalar : ∀ (i : I) (r : Rᵐᵒᵖ) (x : V i), e i (r • x)=f r.unop i*e i x) :
    (R ⧸ RingHom.ker f.toRingHom)ᵐᵒᵖ ≃ₗ[Rᵐᵒᵖ] (∀ i, V i) where
  toFun s i := (e i).symm (Ideal.quotientKerAlgEquivOfSurjective hf s.unop i)
  invFun x := MulOpposite.op ((Ideal.quotientKerAlgEquivOfSurjective hf).symm (fun i => e i (x i)))
  left_inv s := by
    apply MulOpposite.unop_injective
    simp only [MulOpposite.unop_op, LinearEquiv.apply_symm_apply]
    exact (Ideal.quotientKerAlgEquivOfSurjective hf).symm_apply_apply s.unop
  right_inv x := by
    funext i
    simp only [MulOpposite.unop_op, AlgEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
  map_add' s t := by
    funext i
    simp only [MulOpposite.unop_add,map_add,Pi.add_apply]
  map_smul' r s := by
    funext i
    apply (e i).injective
    change (e i) ((e i).symm (Ideal.quotientKerAlgEquivOfSurjective hf (r • s).unop i))=
      e i (r • (e i).symm (Ideal.quotientKerAlgEquivOfSurjective hf s.unop i))
    rw [LinearEquiv.apply_symm_apply,hscalar,LinearEquiv.apply_symm_apply]
    change Ideal.quotientKerAlgEquivOfSurjective hf
        (s.unop * Ideal.Quotient.mk (RingHom.ker f.toRingHom) r.unop) i=
      f r.unop i*Ideal.quotientKerAlgEquivOfSurjective hf s.unop i
    rw [map_mul]
    change _ * f r.unop i=f r.unop i*_
    exact mul_comm _ _

end ASGinzburg
