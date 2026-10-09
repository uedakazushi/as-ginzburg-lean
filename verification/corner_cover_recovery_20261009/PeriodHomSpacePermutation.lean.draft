import ASGinzburg.PeriodIntegerSuccessors

/-! A genuine period acts as a permutation on the disjoint union of all
component elements. Its integer iterates are the ordinary group powers,
which keeps the integer coherence proofs independent of endpoint casts. -/
namespace ASGinzburg.ZAlgebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

abbrev PeriodHomSpace := Σ ij : ℤ × ℤ, A.Hom ij.1 ij.2

theorem homTransport_periodHomSpace (i j i' j' : ℤ) (hi : i=i') (hj : j=j')
    (f : A.Hom i j) :
    (Sigma.mk (i',j') (A.homTransport i j i' j' hi hj f) : A.PeriodHomSpace)=
      Sigma.mk (i,j) f := by
  subst i'
  subst j'
  rfl

namespace PeriodIso
variable {A} {p : ℤ} (E : A.PeriodIso p)

noncomputable def homSpacePerm : Equiv.Perm A.PeriodHomSpace :=
  Equiv.sigmaCongr ((Equiv.addRight p).prodCongr (Equiv.addRight p))
    (fun ij => (E.map ij.1 ij.2).toEquiv)

theorem homSpacePerm_apply (i j : ℤ) (f : A.Hom i j) :
    E.homSpacePerm ⟨(i,j),f⟩=⟨(i+p,j+p),E.map i j f⟩ := rfl

theorem powInt_homSpacePerm_zero : (E.powInt 0).homSpacePerm=1 := by
  apply Equiv.ext
  rintro ⟨⟨i,j⟩,f⟩
  change (Sigma.mk (i+(0:ℤ)*p,j+(0:ℤ)*p) ((E.powNat 0).map i j f) :
    A.PeriodHomSpace)=Sigma.mk (i,j) f
  rw [E.powNat_zero_apply]
  exact A.homTransport_periodHomSpace i j (i+(0:ℤ)*p) (j+(0:ℤ)*p) (by ring) (by ring) f

theorem powInt_homSpacePerm_succ (n : ℤ) :
    (E.powInt (n+1)).homSpacePerm=E.homSpacePerm * (E.powInt n).homSpacePerm := by
  apply Equiv.ext
  rintro ⟨⟨i,j⟩,f⟩
  change (Sigma.mk (i+(n+1)*p,j+(n+1)*p) ((E.powInt (n+1)).map i j f) :
    A.PeriodHomSpace)=
      Sigma.mk ((i+n*p)+p,(j+n*p)+p)
        (E.map (i+n*p) (j+n*p) ((E.powInt n).map i j f))
  rw [E.powInt_succ_apply]
  exact A.homTransport_periodHomSpace _ _ _ _ (by ring) (by ring) _

theorem powInt_homSpacePerm (n : ℤ) : (E.powInt n).homSpacePerm=E.homSpacePerm ^ n := by
  induction n using Int.induction_on with
  | zero => rw [E.powInt_homSpacePerm_zero,zpow_zero]
  | succ n ih =>
    rw [E.powInt_homSpacePerm_succ,ih]
    simpa only [zpow_one,add_comm] using (zpow_add E.homSpacePerm 1 (n:ℤ)).symm
  | pred n ih =>
    apply mul_left_cancel (a := E.homSpacePerm)
    calc
      E.homSpacePerm * (E.powInt (-(n:ℤ)-1)).homSpacePerm =
          (E.powInt (-(n:ℤ))).homSpacePerm := by
        have h := E.powInt_homSpacePerm_succ (-(n:ℤ)-1)
        have hn : -(n:ℤ)-1+1=-(n:ℤ) := by ring
        rw [hn] at h
        exact h.symm
      _ = E.homSpacePerm ^ (-(n:ℤ)) := ih
      _ = E.homSpacePerm * E.homSpacePerm ^ (-(n:ℤ)-1) := by
        calc
          _ = E.homSpacePerm ^ (1+(-(n:ℤ)-1)) := by congr 1; ring
          _ = E.homSpacePerm ^ (1:ℤ) * E.homSpacePerm ^ (-(n:ℤ)-1) :=
            zpow_add E.homSpacePerm 1 (-(n:ℤ)-1)
          _ = _ := by rw [zpow_one]

theorem powInt_homSpacePerm_add (r s : ℤ) :
    (E.powInt (r+s)).homSpacePerm=(E.powInt s).homSpacePerm * (E.powInt r).homSpacePerm := by
  rw [E.powInt_homSpacePerm,E.powInt_homSpacePerm,E.powInt_homSpacePerm,← zpow_add,add_comm]

end PeriodIso
end ASGinzburg.ZAlgebra
