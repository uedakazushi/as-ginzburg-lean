import ASGinzburg.PeriodCutRegularLeftMultiplication
import ASGinzburg.PeriodCutGradedExtFunctor

/-! The underlined Ext space is the actual direct sum over all internal
shifts of the usual regular ring. Homogeneous left multiplication acts
by actual Ext postcomposition into the corresponding shifted target. -/
set_option maxHeartbeats 800000

namespace ASGinzburg.ZAlgebra.PeriodIso
open CategoryTheory
open scoped DirectSum
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

abbrev CutUnderlinedRegularExt (M : E.CutGradedRightModule Q) (n : ℕ) :=
  ⨁ t : ℤ,Abelian.Ext.{v} M ((E.cutRegularGradedRightModule Q).shifted t) n

noncomputable def cutUnderlinedExtHomogeneousOperator (M : E.CutGradedRightModule Q)
    (n m : ℕ) (a : E.CutGradedBlock (fun t : Q.Vertex => (t.val:ℤ)) m) :
    Module.End k (E.CutUnderlinedRegularExt Q M n) :=
  DirectSum.toModule k ℤ _ (fun t =>
    (DirectSum.lof k ℤ
      (fun q => Abelian.Ext.{v} M ((E.cutRegularGradedRightModule Q).shifted q) n)
        (t+(m:ℤ))).comp (cutGradedExtPostcomp (E.cutRegularLeftHomogeneousMap Q m a t) n))

theorem cutUnderlinedExtHomogeneousOperator_lof (M : E.CutGradedRightModule Q)
    (n m : ℕ) (a : E.CutGradedBlock (fun t : Q.Vertex => (t.val:ℤ)) m) (t : ℤ)
    (x : Abelian.Ext.{v} M ((E.cutRegularGradedRightModule Q).shifted t) n) :
    E.cutUnderlinedExtHomogeneousOperator Q M n m a
      (DirectSum.lof k ℤ _ t x)=
        DirectSum.lof k ℤ _ (t+(m:ℤ))
          (x.comp (Abelian.Ext.mk₀ (E.cutRegularLeftHomogeneousMap Q m a t)) (Nat.add_zero n)) :=
by
  change DirectSum.toModule k ℤ _
    (fun s => (DirectSum.lof k ℤ
      (fun q => Abelian.Ext.{v} M ((E.cutRegularGradedRightModule Q).shifted q) n)
        (s+(m:ℤ))).comp (cutGradedExtPostcomp (E.cutRegularLeftHomogeneousMap Q m a s) n))
      (DirectSum.lof k ℤ _ t x)=_
  rw [DirectSum.toModule_lof]
  rfl

end ASGinzburg.ZAlgebra.PeriodIso
