import ASGinzburg.UnrolledPathPresentationMorphism
import Mathlib.LinearAlgebra.Isomorphisms

/-! Kernels of actual componentwise algebra maps are genuine two-sided
linear ideals. Surjective maps identify component quotients with the target. -/
namespace ASGinzburg.ZAlgebra
universe u v w
variable {k : Type u} [Field k] (B : ZAlgebra.{u,v} k)

structure LinearIdeal where
  hom : ∀ i j, Submodule k (B.Hom i j)
  comp_left : ∀ {i j l} {f : B.Hom i j}, f ∈ hom i j →
    ∀ g : B.Hom j l, B.comp g f ∈ hom i l
  comp_right : ∀ {i j l} {g : B.Hom j l}, g ∈ hom j l →
    ∀ f : B.Hom i j, B.comp g f ∈ hom i l

namespace Homomorphism
variable {B} {A : ZAlgebra.{u,w} k} (F : Homomorphism B A)

def kernel : B.LinearIdeal where
  hom i j := LinearMap.ker (F.map i j)
  comp_left := by
    intro i j l f hf g
    change F.map i l (B.comp g f) = 0
    rw [F.map_comp,hf,map_zero]
  comp_right := by
    intro i j l g hg f
    change F.map i l (B.comp g f) = 0
    rw [F.map_comp,hg]
    simp

theorem diagonal_injective (i : ℤ) : Function.Injective (F.map i i) := by
  intro x y h
  obtain ⟨c,hc⟩ := B.connected i x
  obtain ⟨d,hd⟩ := B.connected i y
  rw [hc,hd,map_smul,map_smul,F.map_id] at h
  have hcd : c=d := (A.scalarEndEquiv i).injective h
  rw [hc,hd,hcd]

theorem kernel_diagonal_eq_bot (i : ℤ) : F.kernel.hom i i = ⊥ :=
  LinearMap.ker_eq_bot.mpr (F.diagonal_injective i)

noncomputable def componentQuotientEquiv (hF : ∀ i j, Function.Surjective (F.map i j))
    (i j : ℤ) : (B.Hom i j ⧸ F.kernel.hom i j) ≃ₗ[k] A.Hom i j :=
  (F.map i j).quotKerEquivOfSurjective (hF i j)

theorem componentQuotientEquiv_apply_mk (hF : ∀ i j, Function.Surjective (F.map i j))
    {i j : ℤ} (f : B.Hom i j) :
    F.componentQuotientEquiv hF i j (Submodule.Quotient.mk f) = F.map i j f := rfl

end Homomorphism
end ASGinzburg.ZAlgebra
