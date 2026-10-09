import ASGinzburg.PeriodCutGradedAssociativity

/-! The actual degree-zero units act as units for the shifted
cut multiplication, with its degree-zero reassociation transport. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k} {p : ℤ}
variable (E : A.PeriodIso p)

noncomputable def cutGradedId (i : ℤ) : E.CutGradedHom 0 i i :=
  A.homTransport i i i (i+(0:ℤ)*p) rfl (by ring) (A.id i)

theorem cutGradedComp_id_right (m : ℕ) {i j : ℤ} (f : E.CutGradedHom m i j) :
    E.cutGradedComp m 0 (E.cutGradedId j) f=f := by
  rw [E.cutGradedComp_apply,cutGradedId]
  change A.homTransport i ((j+(0:ℤ)*p)+(m:ℤ)*p) i (j+(m:ℤ)*p) rfl _
    (A.comp ((E.powNat m).map j (j+(0:ℤ)*p)
      (A.homTransport j j j (j+(0:ℤ)*p) rfl _ (A.id j))) f)=f
  have he := PeriodIso.map_homTransport A (E.powNat m) j j j (j+(0:ℤ)*p)
    rfl (by ring) (A.id j)
  rw [he,(E.powNat m).map_id]
  have hc := A.homTransport_comp_target i (j+(m:ℤ)*p) (j+(m:ℤ)*p)
    ((j+(0:ℤ)*p)+(m:ℤ)*p) (by ring) f (A.id (j+(m:ℤ)*p))
  rw [hc,A.homTransport_trans,A.comp_id]
  rfl

theorem cutGradedComp_id_left (m : ℕ) {i j : ℤ} (f : E.CutGradedHom m i j) :
    A.homTransport i (j+((0+m:ℕ):ℤ)*p) i (j+(m:ℤ)*p) rfl (by rw [Nat.zero_add])
      (E.cutGradedComp 0 m f (E.cutGradedId i))=f := by
  rw [E.cutGradedComp_apply,cutGradedId,E.powNat_zero_apply]
  change A.homTransport i (j+((0+m:ℕ):ℤ)*p) i (j+(m:ℤ)*p) rfl _
    (A.homTransport i ((j+(m:ℤ)*p)+(0:ℤ)*p) i (j+((0+m:ℕ):ℤ)*p) rfl _
      (A.comp (A.homTransport i (j+(m:ℤ)*p) (i+(0:ℤ)*p)
        ((j+(m:ℤ)*p)+(0:ℤ)*p) _ _ f)
        (A.homTransport i i i (i+(0:ℤ)*p) rfl _ (A.id i))))=f
  have hc := A.homTransport_comp i i (j+(m:ℤ)*p) i (i+(0:ℤ)*p)
    ((j+(m:ℤ)*p)+(0:ℤ)*p) rfl (by ring) (by ring) (A.id i) f
  rw [← hc,A.homTransport_trans,A.homTransport_trans,A.id_comp]
  rfl

end ASGinzburg.ZAlgebra.PeriodIso
