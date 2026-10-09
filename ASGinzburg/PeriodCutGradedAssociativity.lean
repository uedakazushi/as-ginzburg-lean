import ASGinzburg.PeriodCutGradedComponents

/-! The shifted nonnegative cut multiplication is associative,
with the genuine grading reassociation recorded as an index transport. -/
namespace ASGinzburg.ZAlgebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

theorem homTransport_comp_target (i j l l' : ℤ) (hl : l=l')
    (f : A.Hom i j) (g : A.Hom j l) :
    A.comp (A.homTransport j l j l' rfl hl g) f =
      A.homTransport i l i l' rfl hl (A.comp g f) := by
  subst l'
  rfl

namespace PeriodIso
variable {A} {p : ℤ} (E : A.PeriodIso p)

theorem cutGradedComp_assoc (m n q : ℕ) {i j l s : ℤ}
    (f : E.CutGradedHom m i j) (g : E.CutGradedHom n j l) (h : E.CutGradedHom q l s) :
    E.cutGradedComp (m+n) q h (E.cutGradedComp m n g f) =
      A.homTransport i (s+((m+(n+q):ℕ):ℤ)*p) i (s+(((m+n)+q:ℕ):ℤ)*p)
        rfl (by rw [Nat.add_assoc])
        (E.cutGradedComp m (n+q) (E.cutGradedComp n q h g) f) := by
  rw [E.cutGradedComp_apply,E.cutGradedComp_apply,E.cutGradedComp_apply,E.cutGradedComp_apply]
  rw [E.powNat_add_apply_rev,PeriodIso.map_homTransport,(E.powNat m).map_comp]
  rw [← A.homTransport_comp,A.homTransport_trans,A.homTransport_comp_target,
    A.homTransport_trans,A.homTransport_trans,A.comp_assoc]

end PeriodIso
end ASGinzburg.ZAlgebra
