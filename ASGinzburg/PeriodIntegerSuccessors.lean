import ASGinzburg.PeriodInverseCancellation

/-! All integer period iterates obey the actual one-step recurrence,
including the negative sheets and the -1/0 boundary. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k} {p : ℤ}

theorem map_inverse_powNat_succ (E : A.PeriodIso p) (n : ℕ) (i j : ℤ)
    (f : A.Hom i j) :
    A.homTransport
      ((i + ((n + 1 : ℕ) : ℤ) * (-p)) + p)
      ((j + ((n + 1 : ℕ) : ℤ) * (-p)) + p)
      (i + (n : ℤ) * (-p)) (j + (n : ℤ) * (-p))
      (by push_cast; ring) (by push_cast; ring)
      (E.map (i + ((n + 1 : ℕ) : ℤ) * (-p))
        (j + ((n + 1 : ℕ) : ℤ) * (-p))
        ((E.inverse.powNat (n + 1)).map i j f)) =
      (E.inverse.powNat n).map i j f := by
  rw [powNat_succ_apply, map_homTransport, ASGinzburg.ZAlgebra.homTransport_trans]
  exact E.map_inverse_cancel (i + (n : ℤ) * (-p))
    (j + (n : ℤ) * (-p)) ((E.inverse.powNat n).map i j f)

end ASGinzburg.ZAlgebra.PeriodIso

namespace ASGinzburg.ZAlgebra.PeriodIso
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k} {p : ℤ}

theorem powInt_neg_nat_apply (E : A.PeriodIso p) (n : ℕ) (i j : ℤ)
    (f : A.Hom i j) :
    (E.powInt (-(n : ℤ))).map i j f =
      A.homTransport (i + (n : ℤ) * (-p)) (j + (n : ℤ) * (-p))
        (i + (-(n : ℤ)) * p) (j + (-(n : ℤ)) * p)
        (by ring) (by ring) ((E.inverse.powNat n).map i j f) := by
  cases n with
  | zero =>
    change (E.powNat 0).map i j f =
      A.homTransport (i+(0 : ℤ)*(-p)) (j+(0 : ℤ)*(-p))
        (i+(0 : ℤ)*p) (j+(0 : ℤ)*p) (by ring) (by ring)
        ((E.inverse.powNat 0).map i j f)
    apply (A.homTransport (i+(0 : ℤ)*p) (j+(0 : ℤ)*p) i j
      (by ring) (by ring)).injective
    rw [ASGinzburg.ZAlgebra.homTransport_trans, E.powNat_zero_map,
      E.inverse.powNat_zero_map]
  | succ n =>
    change (E.powInt (Int.negSucc n)).map i j f = _
    rw [powInt, changePeriod_map]
    rfl

theorem powInt_negSucc_apply (E : A.PeriodIso p) (n : ℕ) (i j : ℤ)
    (f : A.Hom i j) :
    (E.powInt (Int.negSucc n)).map i j f =
      A.homTransport (i + ((n + 1 : ℕ) : ℤ) * (-p))
        (j + ((n + 1 : ℕ) : ℤ) * (-p))
        (i + Int.negSucc n * p) (j + Int.negSucc n * p)
        (by rw [Int.negSucc_eq]; push_cast; ring)
        (by rw [Int.negSucc_eq]; push_cast; ring)
        ((E.inverse.powNat (n + 1)).map i j f) := by
  rw [powInt, changePeriod_map]

theorem powInt_map_transport (E : A.PeriodIso p) (r s : ℤ) (h : r = s)
    (i j i' j' : ℤ) (hi : i + r*p = i') (hj : j + r*p = j') (f : A.Hom i j) :
    A.homTransport (i+r*p) (j+r*p) i' j' hi hj ((E.powInt r).map i j f) =
      A.homTransport (i+s*p) (j+s*p) i' j'
        ((congrArg (fun t => i+t*p) h.symm).trans hi)
        ((congrArg (fun t => j+t*p) h.symm).trans hj) ((E.powInt s).map i j f) := by
  subst s
  rfl

theorem powInt_succ_apply (E : A.PeriodIso p) (n i j : ℤ) (f : A.Hom i j) :
    (E.powInt (n + 1)).map i j f =
      A.homTransport ((i + n * p) + p) ((j + n * p) + p)
        (i + (n + 1) * p) (j + (n + 1) * p) (by ring) (by ring)
        (E.map (i + n * p) (j + n * p) ((E.powInt n).map i j f)) := by
  cases n with
  | ofNat n =>
    exact E.powNat_succ_apply n i j f
  | negSucc n =>
    have hn : Int.negSucc n + 1 = -(n : ℤ) := by omega
    apply (A.homTransport (i + (Int.negSucc n + 1) * p)
      (j + (Int.negSucc n + 1) * p) (i + (n : ℤ) * (-p))
      (j + (n : ℤ) * (-p)) (by rw [hn]; ring) (by rw [hn]; ring)).injective
    rw [E.powInt_map_transport (Int.negSucc n + 1) (-(n : ℤ)) hn, powInt_neg_nat_apply, powInt_negSucc_apply, map_homTransport,
      ASGinzburg.ZAlgebra.homTransport_trans, ASGinzburg.ZAlgebra.homTransport_trans,
      ASGinzburg.ZAlgebra.homTransport_trans]
    change (E.inverse.powNat n).map i j f = _
    exact (E.map_inverse_powNat_succ n i j f).symm

end ASGinzburg.ZAlgebra.PeriodIso
