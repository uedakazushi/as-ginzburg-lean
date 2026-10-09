import ASGinzburg.PeriodIntegerSuccessors

/-! Natural powers of a genuine multiplicative period satisfy the
addition law with all component index transports made explicit. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k} {p : ℤ}
variable (E : A.PeriodIso p)

theorem powNat_map_transport (m n : ℕ) (h : m=n) (i j i' j' : ℤ)
    (hi : i+(m:ℤ)*p=i') (hj : j+(m:ℤ)*p=j') (f : A.Hom i j) :
    A.homTransport (i+(n:ℤ)*p) (j+(n:ℤ)*p) i' j'
        ((congrArg (fun t : ℕ => i+(t:ℤ)*p) h.symm).trans hi)
        ((congrArg (fun t : ℕ => j+(t:ℤ)*p) h.symm).trans hj)
        ((E.powNat n).map i j f) =
      A.homTransport (i+(m:ℤ)*p) (j+(m:ℤ)*p) i' j' hi hj ((E.powNat m).map i j f) := by
  subst n
  rfl

theorem powNat_add_apply (m n : ℕ) (i j : ℤ) (f : A.Hom i j) :
    (E.powNat (m+n)).map i j f =
      A.homTransport ((i+(m:ℤ)*p)+(n:ℤ)*p) ((j+(m:ℤ)*p)+(n:ℤ)*p)
        (i+((m+n:ℕ):ℤ)*p) (j+((m+n:ℕ):ℤ)*p)
        (by push_cast; ring) (by push_cast; ring)
        ((E.powNat n).map (i+(m:ℤ)*p) (j+(m:ℤ)*p) ((E.powNat m).map i j f)) := by
  induction n with
  | zero =>
    change (E.powNat m).map i j f =
      A.homTransport ((i+(m:ℤ)*p)+(0:ℤ)*p) ((j+(m:ℤ)*p)+(0:ℤ)*p)
        (i+(m:ℤ)*p) (j+(m:ℤ)*p) _ _
        ((E.powNat 0).map (i+(m:ℤ)*p) (j+(m:ℤ)*p) ((E.powNat m).map i j f))
    exact (E.powNat_zero_map _ _ _).symm
  | succ n ih =>
    change (E.powNat ((m+n)+1)).map i j f =
      A.homTransport ((i+(m:ℤ)*p)+((n+1:ℕ):ℤ)*p) ((j+(m:ℤ)*p)+((n+1:ℕ):ℤ)*p)
        (i+(((m+n)+1:ℕ):ℤ)*p) (j+(((m+n)+1:ℕ):ℤ)*p) _ _
        ((E.powNat (n+1)).map (i+(m:ℤ)*p) (j+(m:ℤ)*p) ((E.powNat m).map i j f))
    rw [E.powNat_succ_apply,ih,E.powNat_succ_apply]
    rw [PeriodIso.map_homTransport,A.homTransport_trans,A.homTransport_trans]

theorem powNat_add_apply_rev (m n : ℕ) (i j : ℤ) (f : A.Hom i j) :
    (E.powNat (m+n)).map i j f =
      A.homTransport ((i+(n:ℤ)*p)+(m:ℤ)*p) ((j+(n:ℤ)*p)+(m:ℤ)*p)
        (i+((m+n:ℕ):ℤ)*p) (j+((m+n:ℕ):ℤ)*p)
        (by push_cast; ring) (by push_cast; ring)
        ((E.powNat m).map (i+(n:ℤ)*p) (j+(n:ℤ)*p) ((E.powNat n).map i j f)) := by
  calc
    _ = A.homTransport (i+((n+m:ℕ):ℤ)*p) (j+((n+m:ℕ):ℤ)*p)
        (i+((m+n:ℕ):ℤ)*p) (j+((m+n:ℕ):ℤ)*p) (by push_cast; ring) (by push_cast; ring)
        ((E.powNat (n+m)).map i j f) := by
      exact E.powNat_map_transport (n+m) (m+n) (Nat.add_comm n m) i j
        (i+((m+n:ℕ):ℤ)*p) (j+((m+n:ℕ):ℤ)*p)
        (by push_cast; ring) (by push_cast; ring) f
    _ = _ := by
      rw [E.powNat_add_apply,A.homTransport_trans]

end ASGinzburg.ZAlgebra.PeriodIso
