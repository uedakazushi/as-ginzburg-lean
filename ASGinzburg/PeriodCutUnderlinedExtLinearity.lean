import ASGinzburg.PeriodCutUnderlinedExtProducts
import ASGinzburg.PeriodCutGradedExtScalarComposition

/-! The actual homogeneous Ext operators are k-linear in the ring
coefficient, as required for extending them over the true direct-sum ring. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open CategoryTheory
open scoped DirectSum
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

theorem cutRegularLeftHomogeneousMap_add (m : ℕ)
    (a b : E.CutGradedBlock (fun t : Q.Vertex => (t.val:ℤ)) m) (t : ℤ) :
    E.cutRegularLeftHomogeneousMap Q m (a+b) t=
      E.cutRegularLeftHomogeneousMap Q m a t+E.cutRegularLeftHomogeneousMap Q m b t := by
  apply Subtype.ext
  change E.cutRegularLeftHomogeneousLinearMap Q m (a+b)=
    E.cutRegularLeftHomogeneousLinearMap Q m a+E.cutRegularLeftHomogeneousLinearMap Q m b
  apply LinearMap.ext
  intro x
  change E.cutHomogeneousInclusion (fun t : Q.Vertex => (t.val:ℤ)) m (a+b)*x=
    E.cutHomogeneousInclusion (fun t : Q.Vertex => (t.val:ℤ)) m a*x+
      E.cutHomogeneousInclusion (fun t : Q.Vertex => (t.val:ℤ)) m b*x
  rw [map_add,add_mul]

theorem cutRegularLeftHomogeneousMap_smul (m : ℕ) (c : k)
    (a : E.CutGradedBlock (fun t : Q.Vertex => (t.val:ℤ)) m) (t : ℤ) :
    E.cutRegularLeftHomogeneousMap Q m (c • a) t=c • E.cutRegularLeftHomogeneousMap Q m a t := by
  apply Subtype.ext
  change E.cutRegularLeftHomogeneousLinearMap Q m (c • a)=c • E.cutRegularLeftHomogeneousLinearMap Q m a
  apply LinearMap.ext
  intro x
  change E.cutHomogeneousInclusion (fun t : Q.Vertex => (t.val:ℤ)) m (c • a)*x=
    c • (E.cutHomogeneousInclusion (fun t : Q.Vertex => (t.val:ℤ)) m a*x)
  rw [show E.cutHomogeneousInclusion (fun t : Q.Vertex => (t.val:ℤ)) m (c • a)=
    c • E.cutHomogeneousInclusion (fun t : Q.Vertex => (t.val:ℤ)) m a from
      E.cutHomogeneousLinearInclusion_smul _ m c a,Algebra.smul_mul_assoc]

noncomputable def cutUnderlinedExtHomogeneousComponent (M : E.CutGradedRightModule Q)
    (n m : ℕ) : E.CutGradedBlock (fun t : Q.Vertex => (t.val:ℤ)) m →ₗ[k]
      Module.End k (E.CutUnderlinedRegularExt Q M n) where
  toFun := E.cutUnderlinedExtHomogeneousOperator Q M n m
  map_add' a b := by
    apply DFinsupp.lhom_ext
    intro t x
    change E.cutUnderlinedExtHomogeneousOperator Q M n m (a+b) (DirectSum.lof k ℤ _ t x)=
      E.cutUnderlinedExtHomogeneousOperator Q M n m a (DirectSum.lof k ℤ _ t x)+
        E.cutUnderlinedExtHomogeneousOperator Q M n m b (DirectSum.lof k ℤ _ t x)
    rw [E.cutUnderlinedExtHomogeneousOperator_lof,E.cutUnderlinedExtHomogeneousOperator_lof,
      E.cutUnderlinedExtHomogeneousOperator_lof,E.cutRegularLeftHomogeneousMap_add,
      Abelian.Ext.mk₀_add,Abelian.Ext.comp_add,map_add]
  map_smul' c a := by
    apply DFinsupp.lhom_ext
    intro t x
    change E.cutUnderlinedExtHomogeneousOperator Q M n m (c • a) (DirectSum.lof k ℤ _ t x)=
      c • E.cutUnderlinedExtHomogeneousOperator Q M n m a (DirectSum.lof k ℤ _ t x)
    rw [E.cutUnderlinedExtHomogeneousOperator_lof,E.cutUnderlinedExtHomogeneousOperator_lof,
      E.cutRegularLeftHomogeneousMap_smul,cutGradedExt_mk₀_smul,cutGradedExt_comp_smul,map_smul]

end ASGinzburg.ZAlgebra.PeriodIso
