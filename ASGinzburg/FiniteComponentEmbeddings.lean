import ASGinzburg.FiniteComponentAlgebra

/-! Actual matrix components and their convolution products in a
finite component algebra. These supply the idempotents used to recover
original component modules from ordinary modules over the total ring. -/
namespace ASGinzburg.LinearComponentAlgebra
universe u v
variable {k : Type u} [Field k] {ι : Type v} [Fintype ι]
  (B : LinearComponentAlgebra k ι)

noncomputable def totalComponent (i j : ι) (a : B.Hom i j) : B.Total := by
  classical
  exact Pi.single i (Pi.single j a)

omit [Fintype ι] in
@[simp] theorem totalComponent_apply_same (i j : ι) (a : B.Hom i j) :
    B.totalComponent i j a i j=a := by
  classical
  simp [totalComponent]

omit [Fintype ι] in
theorem totalComponent_apply_source_ne (i j p q : ι) (a : B.Hom i j) (h : p≠i) :
    B.totalComponent i j a p q=0 := by
  classical
  simp [totalComponent,h]

theorem totalComponent_mul_same (i j l : ι) (f : B.Hom i j) (g : B.Hom j l) :
    B.totalComponent j l g*B.totalComponent i j f=B.totalComponent i l (B.comp g f) := by
  classical
  funext p q
  change (∑ m, B.comp (B.totalComponent j l g m q) (B.totalComponent i j f p m))=_
  by_cases hp : p=i
  · subst p
    by_cases hq : q=l
    · subst q
      rw [Finset.sum_eq_single j]
      · simp [totalComponent]
      · intro m _ hm
        simp [totalComponent,hm]
      · simp
    · simp [totalComponent,hq]
      apply Finset.sum_eq_zero
      intro m _
      by_cases hm : m=j
      · subst m
        simp [hq]
      · simp [hm]
  · simp [totalComponent,hp]

theorem totalComponent_mul_of_ne (i j p q : ι) (f : B.Hom i j) (g : B.Hom p q)
    (h : i≠q) : B.totalComponent i j f*B.totalComponent p q g=0 := by
  classical
  funext a b
  change (∑ m, B.comp (B.totalComponent i j f m b) (B.totalComponent p q g a m))=0
  apply Finset.sum_eq_zero
  intro m _
  by_cases hm : m=i
  · subst m
    by_cases ha : a=p
    · subst a
      simp [totalComponent,h]
    · simp [totalComponent,ha]
  · simp [totalComponent,hm]

theorem sum_totalComponent_id : (∑ i : ι, B.totalComponent i i (B.id i))=1 := by
  classical
  funext p q
  change (∑ i : ι, B.totalComponent i i (B.id i)) p q=B.totalOne p q
  simp only [Finset.sum_apply]
  rw [Finset.sum_eq_single p]
  · by_cases h : p=q
    · subst q
      simp [totalComponent,totalOne]
    · simp [totalComponent,totalOne,h,Ne.symm h]
  · intro i _ hi
    simp [totalComponent,Ne.symm hi]
  · simp

end ASGinzburg.LinearComponentAlgebra
