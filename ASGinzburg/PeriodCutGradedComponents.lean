import ASGinzburg.PeriodNaturalAddition

/-! Actual nonnegative cut-graded components and their shifted
bilinear multiplication, as used to descend a period to a graded algebra. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k} {p : ℤ}
variable (E : A.PeriodIso p)

abbrev CutGradedHom (_E : A.PeriodIso p) (m : ℕ) (i j : ℤ) := A.Hom i (j+(m:ℤ)*p)

noncomputable def cutGradedComp (m n : ℕ) {i j l : ℤ} :
    E.CutGradedHom n j l →ₗ[k] E.CutGradedHom m i j →ₗ[k] E.CutGradedHom (m+n) i l where
  toFun g :=
    (A.homTransport i ((l+(n:ℤ)*p)+(m:ℤ)*p) i (l+((m+n:ℕ):ℤ)*p)
      rfl (by push_cast; ring)).toLinearMap.comp
        (A.comp ((E.powNat m).map j (l+(n:ℤ)*p) g))
  map_add' := by
    intro g h
    ext f
    simp only [LinearMap.comp_apply,map_add,LinearMap.add_apply]
  map_smul' := by
    intro c g
    ext f
    simp only [LinearMap.comp_apply,map_smul,LinearMap.smul_apply,RingHom.id_apply]

theorem cutGradedComp_apply (m n : ℕ) {i j l : ℤ}
    (f : E.CutGradedHom m i j) (g : E.CutGradedHom n j l) :
    E.cutGradedComp m n g f =
      A.homTransport i ((l+(n:ℤ)*p)+(m:ℤ)*p) i (l+((m+n:ℕ):ℤ)*p)
        rfl (by push_cast; ring) (A.comp ((E.powNat m).map j (l+(n:ℤ)*p) g) f) := rfl

end ASGinzburg.ZAlgebra.PeriodIso
