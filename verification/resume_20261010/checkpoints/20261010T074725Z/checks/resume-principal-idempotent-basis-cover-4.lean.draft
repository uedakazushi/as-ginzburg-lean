import work.ASGinzburgDraft.PrincipalIdempotentTop
import work.ASGinzburgDraft.IdempotentPrincipalHom
import Mathlib.LinearAlgebra.Basis.Defs

/-! Lifting an actual basis of the radical quotient into idempotent-fixed
vectors constructs a genuine principal-projective presentation. Its top
map is surjective and its actual kernel lies in the radical action span;
these facts are proved from the basis coordinates. -/
namespace ASGinzburg
open scoped DirectSum ModuleCat.Algebra
universe u v w z
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable {ι : Type w} [DecidableEq ι] (ε : R →ₐ[k] (ι → k))
variable {γ : Type z} [DecidableEq γ] (e : γ → R) (c : γ → ι)
variable (M : ModuleCat.{v} R) (x : γ → M)

noncomputable def principalIdempotentBasisCoverMap :
    (⨁ a, principalIdempotentModule R (e a)) →ₗ[R] M :=
  DirectSum.toModule R γ M (fun a => (principalIdempotentMap R (e a) M (x a)).hom)

theorem principalIdempotentBasisCoverMap_of (a : γ) (p : principalIdempotentModule R (e a)) :
    principalIdempotentBasisCoverMap R e M x (DirectSum.of _ a p) = p.val • x a := by
  change DirectSum.toModule R γ M
    (fun a => (principalIdempotentMap R (e a) M (x a)).hom)
      (DirectSum.lof R γ (fun a => principalIdempotentModule R (e a)) a p) = _
  rw [DirectSum.toModule_lof]
  rfl

noncomputable def principalIdempotentBasisCoverCoordinates :
    (⨁ a, principalIdempotentModule R (e a)) →ₗ[k] (⨁ _ : γ, k) :=
  DirectSum.lmap (fun a => principalIdempotentTopCoordinate k R ε (e a) (c a))

noncomputable def radicalTopBasisDirectSumEquiv
    (B : Module.Basis γ k (M ⧸ ordinaryIdealActionSpan k R M (RingHom.ker ε.toRingHom))) :
    (⨁ _ : γ, k) ≃ₗ[k] (M ⧸ ordinaryIdealActionSpan k R M (RingHom.ker ε.toRingHom)) := by
  classical
  exact (finsuppLequivDFinsupp k).symm.trans B.repr.symm

omit [DecidableEq ι] in
theorem radicalTopBasisDirectSumEquiv_of
    (B : Module.Basis γ k (M ⧸ ordinaryIdealActionSpan k R M (RingHom.ker ε.toRingHom)))
    (a : γ) (r : k) : radicalTopBasisDirectSumEquiv k R ε M B (DirectSum.of _ a r) = r • B a := by
  classical
  change B.repr.symm (DFinsupp.toFinsupp (DFinsupp.single a r)) = _
  rw [DFinsupp.toFinsupp_single, B.repr_symm_single]

include c in
theorem principalIdempotentBasisCover_top_factorization
    (he : ∀ a, e a*e a=e a) (hε : ∀ a, ε (e a)=Pi.single (c a) 1)
    (hx : ∀ a, e a • x a=x a)
    (B : Module.Basis γ k (M ⧸ ordinaryIdealActionSpan k R M (RingHom.ker ε.toRingHom)))
    (hB : ∀ a, (ordinaryIdealActionSpan k R M (RingHom.ker ε.toRingHom)).mkQ (x a)=B a) :
    (ordinaryIdealActionSpan k R M (RingHom.ker ε.toRingHom)).mkQ.comp
      ((principalIdempotentBasisCoverMap R e M x).restrictScalars k) =
    (radicalTopBasisDirectSumEquiv k R ε M B).toLinearMap.comp
      (principalIdempotentBasisCoverCoordinates k R ε e c) := by
  apply DirectSum.linearMap_ext
  intro a
  apply LinearMap.ext
  intro p
  let T := principalIdempotentTopCoordinate k R ε (e a) (c a)
  let g := principalIdempotentGenerator R (e a)
  have hp : p - T p • g ∈ ordinaryIdealActionSpan k R
      (principalIdempotentModule R (e a)) (RingHom.ker ε.toRingHom) := by
    rw [← principalIdempotentTopCoordinate_ker k R ε (e a) (c a) (he a) (hε a)]
    change T (p-T p • g)=0
    rw [map_sub, map_smul]
    change T p - T p • principalIdempotentTopCoordinate k R ε (e a) (c a) g = 0
    rw [principalIdempotentTopCoordinate_generator k R ε (e a) (c a) (hε a)]
    change T p - T p*1 = 0
    rw [mul_one, sub_self]
  have hmap := ordinaryIdealActionSpan_map_mem k R (RingHom.ker ε.toRingHom)
    (principalIdempotentMap R (e a) M (x a)).hom hp
  have hzero := (Submodule.Quotient.mk_eq_zero
    (ordinaryIdealActionSpan k R M (RingHom.ker ε.toRingHom))).mpr hmap
  have hg : (principalIdempotentMap R (e a) M (x a)).hom g = x a :=
    principalIdempotentMap_generator R (e a) M (x a) (hx a)
  change (ordinaryIdealActionSpan k R M (RingHom.ker ε.toRingHom)).mkQ
    ((principalIdempotentMap R (e a) M (x a)).hom (p-T p • g))=0 at hzero
  change (ordinaryIdealActionSpan k R M (RingHom.ker ε.toRingHom)).mkQ
    (principalIdempotentBasisCoverMap R e M x (DirectSum.of _ a p)) =
    radicalTopBasisDirectSumEquiv k R ε M B
      (principalIdempotentBasisCoverCoordinates k R ε e c (DirectSum.of _ a p))
  rw [principalIdempotentBasisCoverMap_of]
  change (ordinaryIdealActionSpan k R M (RingHom.ker ε.toRingHom)).mkQ
    ((principalIdempotentMap R (e a) M (x a)).hom p) = _
  change _ = radicalTopBasisDirectSumEquiv k R ε M B
    (DirectSum.lmap (fun a => principalIdempotentTopCoordinate k R ε (e a) (c a))
      (DirectSum.of _ a p))
  rw [DirectSum.lmap_of, radicalTopBasisDirectSumEquiv_of]
  change _ = T p • B a
  have hm : (principalIdempotentMap R (e a) M (x a)).hom (T p • g) =
      T p • (principalIdempotentMap R (e a) M (x a)).hom g :=
    ((principalIdempotentMap R (e a) M (x a)).hom.restrictScalars k).map_smul (T p) g
  rw [map_sub, hm, hg, map_sub, map_smul, hB a] at hzero
  exact sub_eq_zero.mp hzero

include c in
theorem principalIdempotentBasisCover_kernel_minimal
    (he : ∀ a, e a*e a=e a) (hε : ∀ a, ε (e a)=Pi.single (c a) 1)
    (hx : ∀ a, e a • x a=x a)
    (B : Module.Basis γ k (M ⧸ ordinaryIdealActionSpan k R M (RingHom.ker ε.toRingHom)))
    (hB : ∀ a, (ordinaryIdealActionSpan k R M (RingHom.ker ε.toRingHom)).mkQ (x a)=B a)
    (p : ⨁ a, principalIdempotentModule R (e a))
    (hp : principalIdempotentBasisCoverMap R e M x p=0) :
    p ∈ ordinaryIdealActionSpan k R (⨁ a, principalIdempotentModule R (e a))
      (RingHom.ker ε.toRingHom) := by
  have h := DFunLike.congr_fun
    (principalIdempotentBasisCover_top_factorization k R ε e c M x he hε hx B hB) p
  have hcoord : principalIdempotentBasisCoverCoordinates k R ε e c p=0 := by
    apply (radicalTopBasisDirectSumEquiv k R ε M B).injective
    change radicalTopBasisDirectSumEquiv k R ε M B
        (principalIdempotentBasisCoverCoordinates k R ε e c p) =
      radicalTopBasisDirectSumEquiv k R ε M B 0
    rw [map_zero]
    change (ordinaryIdealActionSpan k R M (RingHom.ker ε.toRingHom)).mkQ
      (principalIdempotentBasisCoverMap R e M x p) =
      radicalTopBasisDirectSumEquiv k R ε M B
        (principalIdempotentBasisCoverCoordinates k R ε e c p) at h
    rw [hp, map_zero] at h
    exact h.symm
  rw [ordinaryIdealActionSpan_directSum_iff k R _ (RingHom.ker ε.toRingHom)]
  intro a
  rw [← principalIdempotentTopCoordinate_ker k R ε (e a) (c a) (he a) (hε a)]
  exact congrArg (fun z => z a) hcoord

omit [DecidableEq γ] in
include c in
theorem principalIdempotentBasisCoverCoordinates_surjective
    (hε : ∀ a, ε (e a)=Pi.single (c a) 1) :
    Function.Surjective (principalIdempotentBasisCoverCoordinates k R ε e c) :=
  (DirectSum.lmap_surjective _).mpr
    (fun a => principalIdempotentTopCoordinate_surjective k R ε (e a) (c a) (hε a))

include c in
theorem principalIdempotentBasisCover_top_surjective
    (he : ∀ a, e a*e a=e a) (hε : ∀ a, ε (e a)=Pi.single (c a) 1)
    (hx : ∀ a, e a • x a=x a)
    (B : Module.Basis γ k (M ⧸ ordinaryIdealActionSpan k R M (RingHom.ker ε.toRingHom)))
    (hB : ∀ a, (ordinaryIdealActionSpan k R M (RingHom.ker ε.toRingHom)).mkQ (x a)=B a) :
    Function.Surjective ((ordinaryIdealActionSpan k R M (RingHom.ker ε.toRingHom)).mkQ.comp
      ((principalIdempotentBasisCoverMap R e M x).restrictScalars k)) := by
  rw [principalIdempotentBasisCover_top_factorization k R ε e c M x he hε hx B hB]
  exact (radicalTopBasisDirectSumEquiv k R ε M B).surjective.comp
    (principalIdempotentBasisCoverCoordinates_surjective k R ε e c hε)

end ASGinzburg
