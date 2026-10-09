import ASGinzburg.PeriodIntegerAddition
import ASGinzburg.PeriodCutGradedUnits

/-! Integer cut components and their actual shifted composition.
These allow the cover multiplication to use all signed sheet differences. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k} {p : ℤ}
variable (E : A.PeriodIso p)

abbrev IntegerCutHom (_E : A.PeriodIso p) (m i j : ℤ) := A.Hom i (j+m*p)

noncomputable def integerCutComp (m n : ℤ) {i j l : ℤ} :
    E.IntegerCutHom n j l →ₗ[k] E.IntegerCutHom m i j →ₗ[k] E.IntegerCutHom (m+n) i l where
  toFun g :=
    (A.homTransport i ((l+n*p)+m*p) i (l+(m+n)*p) rfl (by ring)).toLinearMap.comp
      (A.comp ((E.powInt m).map j (l+n*p) g))
  map_add' := by
    intro g h
    ext f
    simp only [LinearMap.comp_apply,map_add,LinearMap.add_apply]
  map_smul' := by
    intro c g
    ext f
    simp only [LinearMap.comp_apply,map_smul,LinearMap.smul_apply,RingHom.id_apply]

theorem integerCutComp_apply (m n : ℤ) {i j l : ℤ}
    (f : E.IntegerCutHom m i j) (g : E.IntegerCutHom n j l) :
    E.integerCutComp m n g f =
      A.homTransport i ((l+n*p)+m*p) i (l+(m+n)*p) rfl (by ring)
        (A.comp ((E.powInt m).map j (l+n*p) g) f) := rfl

theorem integerCutComp_assoc (m n q : ℤ) {i j l s : ℤ}
    (f : E.IntegerCutHom m i j) (g : E.IntegerCutHom n j l)
    (h : E.IntegerCutHom q l s) :
    E.integerCutComp (m+n) q h (E.integerCutComp m n g f)=
      A.homTransport i (s+(m+(n+q))*p) i (s+((m+n)+q)*p) rfl (by rw [add_assoc])
        (E.integerCutComp m (n+q) (E.integerCutComp n q h g) f) := by
  rw [E.integerCutComp_apply,E.integerCutComp_apply,E.integerCutComp_apply,E.integerCutComp_apply]
  rw [E.powInt_add_apply_rev,PeriodIso.map_homTransport,(E.powInt m).map_comp]
  rw [← A.homTransport_comp,A.homTransport_trans,A.homTransport_comp_target,
    A.homTransport_trans,A.homTransport_trans,A.comp_assoc]

theorem integerCutComp_id_right (m : ℤ) {i j : ℤ} (f : E.IntegerCutHom m i j) :
    A.homTransport i (j+(m+0)*p) i (j+m*p) rfl (by rw [add_zero])
      (E.integerCutComp m 0 (E.cutGradedId j) f)=f := by
  rw [E.integerCutComp_apply,cutGradedId,PeriodIso.map_homTransport,(E.powInt m).map_id]
  rw [A.homTransport_comp_target,A.homTransport_trans,A.homTransport_trans,A.comp_id]
  rfl

theorem integerCutComp_id_left (m : ℤ) {i j : ℤ} (f : E.IntegerCutHom m i j) :
    A.homTransport i (j+(0+m)*p) i (j+m*p) rfl (by rw [zero_add])
      (E.integerCutComp 0 m f (E.cutGradedId i))=f := by
  rw [E.integerCutComp_apply,cutGradedId]
  change A.homTransport i (j+(0+m)*p) i (j+m*p) rfl _
    (A.homTransport i ((j+m*p)+(0:ℤ)*p) i (j+(0+m)*p) rfl _
      (A.comp ((E.powNat 0).map i (j+m*p) f)
        (A.homTransport i i i (i+(0:ℤ)*p) rfl _ (A.id i))))=f
  rw [E.powNat_zero_apply]
  change A.homTransport i (j+(0+m)*p) i (j+m*p) rfl _
    (A.homTransport i ((j+m*p)+(0:ℤ)*p) i (j+(0+m)*p) rfl _
      (A.comp (A.homTransport i (j+m*p) (i+(0:ℤ)*p) ((j+m*p)+(0:ℤ)*p) _ _ f)
        (A.homTransport i i i (i+(0:ℤ)*p) rfl _ (A.id i))))=f
  have hc := A.homTransport_comp i i (j+m*p) i (i+(0:ℤ)*p) ((j+m*p)+(0:ℤ)*p)
    rfl (by ring) (by ring) (A.id i) f
  rw [← hc,A.homTransport_trans,A.homTransport_trans,A.id_comp]
  rfl

theorem integerCutComp_ofNat (m n : ℕ) {i j l : ℤ}
    (f : E.CutGradedHom m i j) (g : E.CutGradedHom n j l) :
    A.homTransport i (l+((m:ℤ)+(n:ℤ))*p) i (l+((m+n:ℕ):ℤ)*p)
      rfl (by push_cast; ring) (E.integerCutComp (m:ℤ) (n:ℤ) g f)=
        E.cutGradedComp m n g f := by
  rw [integerCutComp_apply,cutGradedComp_apply,A.homTransport_trans]
  rfl

end ASGinzburg.ZAlgebra.PeriodIso
