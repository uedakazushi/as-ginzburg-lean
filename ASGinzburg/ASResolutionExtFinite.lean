import ASGinzburg.ASResolutionExtBounds
import ASGinzburg.RightModuleHomFinite

/-!
# Finite-dimensional actual Ext from the AS resolution alone

No total rank or delta table is assumed. The low degrees are quotients of
finite-dimensional Hom spaces, by the actual long exact Ext sequences.
-/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

theorem rightModuleExtZeroFinite (M N : A.RightModule) [Module.Finite k (M ⟶ N)] :
    Module.Finite k (Abelian.Ext.{v} M N 0) :=
  Module.Finite.of_injective (A.rightModuleExtZeroLinearEquiv M N).toLinearMap
    (A.rightModuleExtZeroLinearEquiv M N).injective

/-- Degree-one Ext is a quotient of Hom of the kernel, without requiring Hom vanishing. -/
theorem rightModuleExtOneFinite {S : ShortComplex A.RightModule}
    (hS : S.ShortExact) [Projective S.X₂] (N : A.RightModule)
    [Module.Finite k (S.X₁ ⟶ N)] : Module.Finite k (Abelian.Ext.{v} S.X₃ N 1) := by
  letI := A.rightModuleExtZeroFinite S.X₁ N
  apply Module.Finite.of_surjective (A.rightModuleExtBoundary hS N 0)
  intro x
  exact Abelian.Ext.contravariant_sequence_exact₃ hS N x
    (Abelian.Ext.eq_zero_of_projective _) (by rfl)

namespace ASResolution
variable {A} {Q : CutQuiver} {w : Q.LiftVertex}

/-- The finite AS sequence and local finiteness alone imply finite Ext into every P_i. -/
theorem extFinite_representable (R : A.ASResolution Q w) (i : ℤ) (p : ℕ) :
    Module.Finite k (Abelian.Ext.{v} (A.simpleRightModule (Q.height w))
      (A.representable i) p) := by
  let N := A.representable i
  letI := A.representableHomRepresentableFinite (Q.height w) i
  letI := A.representableHomRepresentableFinite (Q.height (Q.tau.symm w)) i
  letI := A.asResolutionTerm₁HomFinite Q w i
  letI := A.asResolutionTerm₂HomFinite Q w i
  letI := A.rightModuleHomFinite_of_epi R.firstCover N
  letI := A.rightModuleHomFinite_of_epi R.secondCover N
  rcases p with _ | _ | _ | _ | p
  · letI := A.rightModuleHomFinite_of_epi (A.simpleRightModuleπ (Q.height w)) N
    exact A.rightModuleExtZeroFinite _ _
  · exact A.rightModuleExtOneFinite
      (ASResolution.shortExact₀ (A := A) (Q := Q) (v := w)) N
  · letI := A.rightModuleExtOneFinite R.shortExact₁ N
    exact Module.Finite.of_surjective
      (A.rightModuleExtDimensionShift
        (ASResolution.shortExact₀ (A := A) (Q := Q) (v := w)) N 0).toLinearMap
      (A.rightModuleExtDimensionShift
        (ASResolution.shortExact₀ (A := A) (Q := Q) (v := w)) N 0).surjective
  · letI := A.rightModuleExtOneFinite R.shortExact₂ N
    let e := (A.rightModuleExtDimensionShift R.shortExact₁ N 0).trans
      (A.rightModuleExtDimensionShift
        (ASResolution.shortExact₀ (A := A) (Q := Q) (v := w)) N 1)
    exact Module.Finite.of_surjective e.toLinearMap e.surjective
  · letI : Subsingleton (Abelian.Ext.{v} (A.simpleRightModule (Q.height w)) N (p + 4)) :=
      ⟨fun x y => by rw [R.ext_ge_four_eq_zero N p x, R.ext_ge_four_eq_zero N p y]⟩
    infer_instance

end ASResolution
end ASGinzburg.ZAlgebra
