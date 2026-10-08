import ASGinzburg.UnrolledPathFiniteness
import ASGinzburg.ASGeneratorBasis

/-! Actual one-arrow paths are indexed by incoming arrows with the specified
source vertex. The height bijection compares this index with generator bases. -/
namespace ASGinzburg.CutQuiver.UnrolledPath
variable {Q : CutQuiver}

theorem height_eq_of_length_zero {u v : Q.LiftVertex} (p : Q.UnrolledPath u v)
    (hp : p.length=0) : Q.height u = Q.height v := by
  cases p with
  | nil => rfl
  | snoc a p => simp [length] at hp

abbrev SingleArrowIndex (u v : Q.LiftVertex) :=
  {a : Q.incomingArrows v // Q.incomingSource v a = u}

noncomputable def singleArrow (u v : Q.LiftVertex) (a : SingleArrowIndex u v) : Q.UnrolledPath u v := by
  obtain ⟨a,ha⟩ := a
  subst u
  exact .snoc a (.nil _)

theorem singleArrow_length (u v : Q.LiftVertex) (a : SingleArrowIndex u v) :
    (singleArrow u v a).length=1 := by
  obtain ⟨a,ha⟩ := a
  subst u
  rfl

noncomputable def singleArrowOfPath {u v : Q.LiftVertex} (p : Q.UnrolledPath u v)
    (hp : p.length=1) : SingleArrowIndex u v := by
  cases p with
  | nil => simp [length] at hp
  | @snoc v a p =>
    refine ⟨a,?_⟩
    have hz : p.length=0 := by simp only [length] at hp; omega
    exact (Q.height_bijective.injective (p.height_eq_of_length_zero hz)).symm

theorem singleArrowOfPath_singleArrow (u v : Q.LiftVertex) (a : SingleArrowIndex u v) :
    singleArrowOfPath (singleArrow u v a) (singleArrow_length u v a) = a := by
  obtain ⟨a,ha⟩ := a
  subst u
  rfl

theorem singleArrow_singleArrowOfPath {u v : Q.LiftVertex} (p : Q.UnrolledPath u v)
    (hp : p.length=1) : singleArrow u v (singleArrowOfPath p hp) = p := by
  cases p with
  | nil => simp [length] at hp
  | @snoc v a p =>
    have hz : p.length=0 := by simp only [length] at hp; omega
    have hu := Q.height_bijective.injective (p.height_eq_of_length_zero hz)
    subst u
    have hnil := p.diagonal_eq_nil
    cases hnil
    rfl

noncomputable def singleArrowEquiv (u v : Q.LiftVertex) :
    SingleArrowIndex u v ≃ {p : Q.UnrolledPath u v // p.length=1} where
  toFun a := ⟨singleArrow u v a,singleArrow_length u v a⟩
  invFun p := singleArrowOfPath p.val p.property
  left_inv := singleArrowOfPath_singleArrow u v
  right_inv p := Subtype.ext (singleArrow_singleArrowOfPath p.val p.property)

noncomputable def singleArrowHeightEquiv (u v : Q.LiftVertex) :
    SingleArrowIndex u v ≃
      ASGinzburg.ZAlgebra.ASResolution.GeneratorIndex (Q := Q) (w := v) (Q.height u) where
  toFun a := ⟨a.val,congrArg Q.height a.property⟩
  invFun a := ⟨a.val,Q.height_bijective.injective a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

end ASGinzburg.CutQuiver.UnrolledPath
