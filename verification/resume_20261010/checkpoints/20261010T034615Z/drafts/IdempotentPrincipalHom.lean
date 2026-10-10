import work.ASGinzburgDraft.IdempotentPrincipalProjective

/-! Maps from the actual principal projective R e are determined by an
actual target vector fixed by e. The generator formula constructs the
maps used by homogeneous top-basis projective covers. -/
namespace ASGinzburg
open CategoryTheory
universe u
variable (R : Type u) [Ring R]

def principalIdempotentMap (e : R) (M : ModuleCat.{u} R) (x : M) :
    principalIdempotentModule R e ⟶ M :=
  ModuleCat.ofHom (((LinearMap.id : R →ₗ[R] R).smulRight x).comp
    (LinearMap.range (principalIdempotentOperator R e)).subtype)

theorem principalIdempotentMap_apply (e : R) (M : ModuleCat.{u} R) (x : M)
    (y : principalIdempotentModule R e) :
    principalIdempotentMap R e M x y = y.val • x := rfl

theorem principalIdempotentMap_generator (e : R) (M : ModuleCat.{u} R) (x : M)
    (hx : e • x = x) :
    principalIdempotentMap R e M x (principalIdempotentGenerator R e) = x := hx

theorem principalIdempotentGenerator_fixed (e : R) (he : e*e=e) :
    e • principalIdempotentGenerator R e = principalIdempotentGenerator R e :=
  Subtype.ext he

theorem principalIdempotentHom_generator_fixed (e : R) (he : e*e=e)
    (M : ModuleCat.{u} R) (f : principalIdempotentModule R e ⟶ M) :
    e • f (principalIdempotentGenerator R e) = f (principalIdempotentGenerator R e) := by
  rw [← map_smul, principalIdempotentGenerator_fixed R e he]

theorem principalIdempotentHom_ext (e : R) (M : ModuleCat.{u} R)
    (f g : principalIdempotentModule R e ⟶ M)
    (h : f (principalIdempotentGenerator R e) = g (principalIdempotentGenerator R e)) :
    f = g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨r, rfl⟩ := principalIdempotentModule_generator R e x
  rw [map_smul, map_smul, h]

def principalIdempotentHomEquiv (e : R) (he : e*e=e) (M : ModuleCat.{u} R) :
    (principalIdempotentModule R e ⟶ M) ≃ {x : M | e • x = x} where
  toFun f := ⟨f (principalIdempotentGenerator R e),
    principalIdempotentHom_generator_fixed R e he M f⟩
  invFun x := principalIdempotentMap R e M x.val
  left_inv f := principalIdempotentHom_ext R e M _ _
    (principalIdempotentMap_generator R e M _
      (principalIdempotentHom_generator_fixed R e he M f))
  right_inv x := Subtype.ext (principalIdempotentMap_generator R e M x.val x.property)

end ASGinzburg
