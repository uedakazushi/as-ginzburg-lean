import ASGinzburg.ASMinimalGenerators
import Mathlib.LinearAlgebra.Quotient.Basic

namespace ASGinzburg
universe u v w
variable {k : Type u} [Field k] {V : Type v} {W : Type w}
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- A surjective linear map induces the expected quotient isomorphism when
its kernel lies in the subspace being quotiented. -/
noncomputable def surjectiveQuotientImageEquiv (f : V →ₗ[k] W)
    (hf : Function.Surjective f) (p : Submodule k V) (hker : LinearMap.ker f ≤ p) :
    (V ⧸ p) ≃ₗ[k] (W ⧸ p.map f) := by
  let g := p.mapQ (p.map f) f (Submodule.le_comap_map f p)
  refine LinearEquiv.ofBijective g ⟨?_,?_⟩
  · apply LinearMap.ker_eq_bot.mp
    dsimp only [g,Submodule.mapQ]
    rw [Submodule.ker_liftQ,LinearMap.ker_comp,Submodule.ker_mkQ,
      Submodule.comap_map_eq_self hker,Submodule.mkQ_map_self]
  · intro y
    obtain ⟨b,rfl⟩ := (p.map f).mkQ_surjective y
    obtain ⟨a,rfl⟩ := hf b
    exact ⟨p.mkQ a,rfl⟩

namespace ZAlgebra
open CategoryTheory CategoryTheory.Limits
variable {A : ZAlgebra.{u,v} k} {Q : CutQuiver}
namespace ASResolution
variable {w : Q.LiftVertex} (R : A.ASResolution Q w)

noncomputable def indecomposablesEquiv (i : ℤ) (hi : i < Q.height w) :
    ((A.rightModuleEvaluation i).obj (A.asResolutionTerm₁ Q w) ⧸
      A.positiveActionSpan (A.asResolutionTerm₁ Q w) i) ≃ₗ[k]
    (A.Hom i (Q.height w) ⧸ Submodule.span k (A.products i (Q.height w))) :=
  (surjectiveQuotientImageEquiv ((A.rightModuleEvaluation i).map R.d₁).hom
    (R.d₁_component_surjective i hi) _ (R.d₁_component_ker_le_radical i)).trans
    (Submodule.quotEquivOfEq _ _ (R.d₁_radical_image i))

end ASResolution
end ZAlgebra
end ASGinzburg
