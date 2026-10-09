import ASGinzburg.PeriodCutGradedMatrix
import Mathlib.Algebra.DirectSum.Algebra

/-! The multiplication of homogeneous finite blocks, in the ordinary
algebra order, gives mathlib's graded monoid. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
universe u v w
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k} {p : ℤ}
variable (E : A.PeriodIso p) {ι : Type w} [Fintype ι] (vertex : ι → ℤ)

omit [Fintype ι] in
theorem cutBlockTransport_heq (m n : ℕ) (h : m=n) (f : E.CutGradedBlock vertex m) :
    HEq (E.cutBlockTransport vertex m n h f) f := by
  subst n
  rfl

omit [Fintype ι] in
theorem cutBlockTransport_sigma (m n : ℕ) (h : m=n) (f : E.CutGradedBlock vertex m) :
    (Sigma.mk n (E.cutBlockTransport vertex m n h f) : Σ q, E.CutGradedBlock vertex q)=
      Sigma.mk m f := by
  subst n
  rfl

noncomputable def cutHomogeneousProduct
    (x y : Σ m, E.CutGradedBlock vertex m) : Σ m, E.CutGradedBlock vertex m :=
  ⟨y.1+x.1,E.cutMatrixComp vertex y.1 x.1 x.2 y.2⟩

theorem cutHomogeneousProduct_assoc (x y z : Σ m, E.CutGradedBlock vertex m) :
    E.cutHomogeneousProduct vertex (E.cutHomogeneousProduct vertex x y) z=
      E.cutHomogeneousProduct vertex x (E.cutHomogeneousProduct vertex y z) := by
  rcases x with ⟨m,x⟩
  rcases y with ⟨n,y⟩
  rcases z with ⟨q,z⟩
  dsimp only [cutHomogeneousProduct]
  rw [E.cutMatrixComp_assoc]
  exact (E.cutBlockTransport_sigma vertex (q+(n+m)) ((q+n)+m)
    (Nat.add_assoc q n m).symm _).symm

noncomputable def cutBlockMul (m n : ℕ) :
    E.CutGradedBlock vertex m →ₗ[k] E.CutGradedBlock vertex n →ₗ[k]
      E.CutGradedBlock vertex (m+n) where
  toFun x := (E.cutBlockTransport vertex (n+m) (m+n) (Nat.add_comm n m)).toLinearMap.comp
    ((E.cutMatrixComp vertex n m x))
  map_add' := by
    intro x y
    ext z
    simp only [LinearMap.comp_apply,map_add,LinearMap.add_apply]
  map_smul' := by
    intro c x
    ext z
    simp only [LinearMap.comp_apply,map_smul,LinearMap.smul_apply,RingHom.id_apply]

theorem cutBlockMul_sigma (m n : ℕ)
    (x : E.CutGradedBlock vertex m) (y : E.CutGradedBlock vertex n) :
    (Sigma.mk (m+n) (E.cutBlockMul vertex m n x y) : Σ q, E.CutGradedBlock vertex q)=
      E.cutHomogeneousProduct vertex ⟨m,x⟩ ⟨n,y⟩ :=
  E.cutBlockTransport_sigma vertex (n+m) (m+n) (Nat.add_comm n m) _

noncomputable instance cutBlockGOne : GradedMonoid.GOne (E.CutGradedBlock vertex) :=
  ⟨E.cutMatrixId vertex⟩

noncomputable instance cutBlockGMul : GradedMonoid.GMul (E.CutGradedBlock vertex) :=
  ⟨fun {m n} x y => E.cutBlockMul vertex m n x y⟩

theorem cutGradedMonoid_mul_eq (x y : GradedMonoid (E.CutGradedBlock vertex)) :
    x*y=E.cutHomogeneousProduct vertex x y := by
  rcases x with ⟨m,x⟩
  rcases y with ⟨n,y⟩
  exact E.cutBlockMul_sigma vertex m n x y

noncomputable instance cutBlockGMonoid : GradedMonoid.GMonoid (E.CutGradedBlock vertex) where
  one_mul := by
    rintro ⟨m,x⟩
    rw [cutGradedMonoid_mul_eq]
    change (Sigma.mk (m+0) (E.cutMatrixComp vertex m 0 (E.cutMatrixId vertex) x) :
      Σ q, E.CutGradedBlock vertex q)=Sigma.mk m x
    rw [E.cutMatrixComp_id_right]
    rfl
  mul_one := by
    rintro ⟨m,x⟩
    rw [cutGradedMonoid_mul_eq]
    change (Sigma.mk (0+m) (E.cutMatrixComp vertex 0 m x (E.cutMatrixId vertex)) :
      Σ q, E.CutGradedBlock vertex q)=Sigma.mk m x
    calc
      _ = Sigma.mk m (E.cutBlockTransport vertex (0+m) m (Nat.zero_add m)
        (E.cutMatrixComp vertex 0 m x (E.cutMatrixId vertex))) :=
          (E.cutBlockTransport_sigma vertex (0+m) m (Nat.zero_add m) _).symm
      _ = Sigma.mk m x := congrArg (Sigma.mk m) (E.cutMatrixComp_id_left vertex m x)
  mul_assoc := by
    intro x y z
    simp only [cutGradedMonoid_mul_eq]
    exact E.cutHomogeneousProduct_assoc vertex x y z

end ASGinzburg.ZAlgebra.PeriodIso
