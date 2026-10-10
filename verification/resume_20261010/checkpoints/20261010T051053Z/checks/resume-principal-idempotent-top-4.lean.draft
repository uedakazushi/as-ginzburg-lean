import work.ASGinzburgDraft.IdempotentPrincipalProjective
import work.ASGinzburgDraft.OrdinaryIdealActionDirectSum
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! The actual radical top of a principal idempotent projective is the
one-dimensional coordinate singled out by its augmentation. This supplies
basis coordinates for genuine minimal homogeneous projective covers. -/
namespace ASGinzburg
open scoped ModuleCat.Algebra
universe u v w
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable {ι : Type w} [DecidableEq ι]
variable (ε : R →ₐ[k] (ι → k)) (e : R) (i : ι)

def principalIdempotentTopCoordinate : principalIdempotentModule R e →ₗ[k] k where
  toFun x := ε x.val i
  map_add' x y := by
    change ε (x.val+y.val) i = ε x.val i + ε y.val i
    rw [map_add]
    rfl
  map_smul' c x := by
    change ε ((algebraMap k R c)*x.val) i = c*ε x.val i
    rw [map_mul, ε.commutes]
    rfl

omit [DecidableEq ι] in
theorem principalIdempotentTopCoordinate_apply (x : principalIdempotentModule R e) :
    principalIdempotentTopCoordinate k R ε e i x = ε x.val i := rfl

theorem principalIdempotentTopCoordinate_generator
    (hε : ε e = Pi.single i 1) :
    principalIdempotentTopCoordinate k R ε e i (principalIdempotentGenerator R e) = 1 := by
  change ε e i = 1
  rw [hε, Pi.single_eq_same]

theorem principalIdempotentTopCoordinate_surjective
    (hε : ε e = Pi.single i 1) :
    Function.Surjective (principalIdempotentTopCoordinate k R ε e i) := by
  intro a
  refine ⟨a • principalIdempotentGenerator R e, ?_⟩
  rw [map_smul, principalIdempotentTopCoordinate_generator k R ε e i hε]
  exact mul_one a

theorem principalIdempotentTopCoordinate_ker
    (he : e*e=e) (hε : ε e = Pi.single i 1) :
    LinearMap.ker (principalIdempotentTopCoordinate k R ε e i) =
      ordinaryIdealActionSpan k R (principalIdempotentModule R e) (RingHom.ker ε.toRingHom) := by
  apply le_antisymm
  · intro x hx
    have hx0 : ε x.val i = 0 := hx
    have hxe : x.val*e=x.val := by
      obtain ⟨r, hr⟩ := x.property
      change r*e=x.val at hr
      rw [← hr, mul_assoc, he]
    have hxε : ε x.val = 0 := by
      ext j
      by_cases hji : j=i
      · subst j
        exact hx0
      · have h := congrArg (fun r : R => ε r j) hxe
        simpa only [map_mul, Pi.mul_apply, hε, Pi.single_eq_of_ne hji,
          mul_zero, Pi.zero_apply] using h.symm
    apply Submodule.subset_span
    refine ⟨x.val, hxε, principalIdempotentGenerator R e, ?_⟩
    exact Subtype.ext hxe
  · apply Submodule.span_le.mpr
    rintro x ⟨r, hr, p, rfl⟩
    change ε (r*p.val) i = 0
    have hr0 : ε r = 0 := hr
    rw [map_mul, hr0, zero_mul]
    rfl

noncomputable def principalIdempotentTopEquiv
    (he : e*e=e) (hε : ε e = Pi.single i 1) :
    (principalIdempotentModule R e ⧸
      ordinaryIdealActionSpan k R (principalIdempotentModule R e) (RingHom.ker ε.toRingHom)) ≃ₗ[k] k :=
  (Submodule.quotEquivOfEq _ _ (principalIdempotentTopCoordinate_ker k R ε e i he hε).symm).trans
    ((principalIdempotentTopCoordinate k R ε e i).quotKerEquivOfSurjective
      (principalIdempotentTopCoordinate_surjective k R ε e i hε))

end ASGinzburg
