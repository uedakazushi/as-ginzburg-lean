import ASGinzburg.QuotientZAlgebra
import ASGinzburg.PeriodInverse

/-! A genuine multiplicative period preserving an actual ideal
descends to the genuine quotient algebra, with no quotient-period assumption. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
universe u v
variable {k : Type u} [Field k] {B : ZAlgebra.{u,v} k} {p : ℤ}
variable (E : B.PeriodIso p) (I : B.LinearIdeal)
variable (hdiag : ∀ i, I.hom i i=⊥)
variable (hI : ∀ i j, (I.hom i j).map (E.map i j).toLinearMap=I.hom (i+p) (j+p))

noncomputable def idealQuotientPeriod : (I.quotient hdiag).PeriodIso p where
  map i j := Submodule.Quotient.equiv _ _ (E.map i j) (hI i j)
  map_id := by
    intro i
    change Submodule.Quotient.mk (E.map i i (B.id i)) = Submodule.Quotient.mk (B.id (i+p))
    exact congrArg Submodule.Quotient.mk (E.map_id i)
  map_comp := by
    intro i j l f g
    obtain ⟨f,rfl⟩ := (I.hom i j).mkQ_surjective f
    obtain ⟨g,rfl⟩ := (I.hom j l).mkQ_surjective g
    change Submodule.Quotient.mk (E.map i l (B.comp g f)) =
      Submodule.Quotient.mk (B.comp (E.map j l g) (E.map i j f))
    exact congrArg Submodule.Quotient.mk (E.map_comp f g)

theorem idealQuotientPeriod_apply_mk (i j : ℤ) (f : B.Hom i j) :
    (E.idealQuotientPeriod I hdiag hI).map i j (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (E.map i j f) := rfl

end ASGinzburg.ZAlgebra.PeriodIso
