import ASGinzburg.PeriodCutZeroNilpotence
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.Jacobson.Semiprimary

/-! The actual degree-zero Jacobson radical equals the diagonal kernel.
This uses the directed nilpotence bound and the semisimple scalar quotient. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

theorem cutZeroKernel_le_jacobson :
    RingHom.ker (E.cutZeroDiagonalAlgHom Q).toRingHom ≤
      Ring.jacobson (E.CutGradedBlock (fun i : Q.Vertex => (i.val:ℤ)) 0) := by
  intro x hx
  rw [← Ideal.jacobson_bot,Ideal.mem_jacobson_iff]
  intro y
  have hn : IsNilpotent (y*x) := E.cutZeroKernel_isNilpotent Q (y*x) (by
    rw [map_mul]
    change E.cutZeroDiagonalAlgHom Q x=0 at hx
    rw [hx,mul_zero])
  obtain ⟨u,hu⟩ := hn.isUnit_add_one
  refine ⟨↑u⁻¹,?_⟩
  rw [Ideal.mem_bot]
  calc
    (↑u⁻¹)*y*x+↑u⁻¹-1=(↑u⁻¹)*(y*x+1)-1 := by rw [mul_add,mul_one,mul_assoc]
    _=0 := by rw [← hu];simp

theorem cutZeroJacobson_le_kernel :
    Ring.jacobson (E.CutGradedBlock (fun i : Q.Vertex => (i.val:ℤ)) 0) ≤
      RingHom.ker (E.cutZeroDiagonalAlgHom Q).toRingHom := by
  let f := (E.cutZeroDiagonalAlgHom Q).toRingHom
  letI : RingHomSurjective f := ⟨E.cutZeroDiagonalAlgHom_surjective Q⟩
  have h := Ring.le_comap_jacobson (f:=f)
  rw [IsSemisimpleRing.jacobson_eq_bot (Q.Vertex→k)] at h
  exact h

theorem cutZeroJacobson_eq_kernel :
    Ring.jacobson (E.CutGradedBlock (fun i : Q.Vertex => (i.val:ℤ)) 0)=
      RingHom.ker (E.cutZeroDiagonalAlgHom Q).toRingHom :=
  le_antisymm (E.cutZeroJacobson_le_kernel Q) (E.cutZeroKernel_le_jacobson Q)

set_option synthInstance.maxHeartbeats 100000 in
noncomputable def cutZeroSemisimpleQuotientAlgEquiv :
    (E.CutGradedBlock (fun i : Q.Vertex => (i.val:ℤ)) 0 ⧸
      Ring.jacobson (E.CutGradedBlock (fun i : Q.Vertex => (i.val:ℤ)) 0)) ≃ₐ[k]
      (Q.Vertex→k) :=
  (Ideal.quotientEquivAlgOfEq k (E.cutZeroJacobson_eq_kernel Q)).trans
    (Ideal.quotientKerAlgEquivOfSurjective (E.cutZeroDiagonalAlgHom_surjective Q))

end ASGinzburg.ZAlgebra.PeriodIso
