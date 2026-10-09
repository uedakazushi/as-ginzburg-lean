import ASGinzburg.PeriodIntegerAddition

/-! A composited pair of signed periods can be transported directly to
fixed endpoints, so later cover comparisons have no intermediate casts. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k} {p : ℤ}
variable (E : A.PeriodIso p)

theorem powInt_composition_to (r s t : ℤ) (ht : r+s=t) (i j i' j' : ℤ)
    (hi : i+t*p=i') (hj : j+t*p=j') (f : A.Hom i j) :
    A.homTransport ((i+s*p)+r*p) ((j+s*p)+r*p) i' j'
      (by rw [← hi,← ht]; ring) (by rw [← hj,← ht]; ring)
      ((E.powInt r).map (i+s*p) (j+s*p) ((E.powInt s).map i j f)) =
        A.homTransport (i+t*p) (j+t*p) i' j' hi hj ((E.powInt t).map i j f) := by
  calc
    _ = A.homTransport (i+(r+s)*p) (j+(r+s)*p) i' j'
      (by rw [ht]; exact hi) (by rw [ht]; exact hj)
      ((E.powInt (r+s)).map i j f) := by
        rw [E.powInt_add_apply_rev,A.homTransport_trans]
    _ = _ := E.powInt_map_transport (r+s) t ht i j i' j'
      (by rw [ht]; exact hi) (by rw [ht]; exact hj) f

end ASGinzburg.ZAlgebra.PeriodIso
