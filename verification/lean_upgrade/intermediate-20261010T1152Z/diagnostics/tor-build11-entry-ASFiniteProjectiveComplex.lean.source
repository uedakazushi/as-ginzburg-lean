import ASGinzburg.FiniteProjectiveClosure
import ASGinzburg.BoundedCochainDuality
import ASGinzburg.ASResolutionComplex
import Mathlib.Algebra.Homology.Embedding.Extend
namespace ASGinzburg.ZAlgebra.ASResolution
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k} {Q : CutQuiver}
  {w : Q.LiftVertex} (R : A.ASResolution Q w)

theorem complexTermFiniteProjective (n : ℕ) : A.rightFiniteProjectiveProperty (R.complexTerm n) := by
  rcases n with _ | _ | _ | _ | n
  · exact A.rightFiniteProjectiveProperty_representable _
  · exact A.rightFiniteProjectiveProperty_coproduct _
  · exact A.rightFiniteProjectiveProperty_coproduct _
  · exact A.rightFiniteProjectiveProperty_representable _
  · exact A.rightFiniteProjectiveProperty_of_isZero (isZero_zero A.RightModule)

noncomputable def finiteProjectiveComplex : ChainComplex A.RightFiniteProjective ℕ where
  X n := ⟨R.complexTerm n, R.complexTermFiniteProjective n⟩
  d i j := R.complex.d i j
  shape i j hij := R.complex.shape i j hij
  d_comp_d' i j l hij hjl := R.complex.d_comp_d' i j l hij hjl

theorem finiteProjectiveComplex_isZero_ge_four (n : ℕ) :
    IsZero (R.finiteProjectiveComplex.X (n+4)) := by
  rw [IsZero.iff_id_eq_zero]
  change 𝟙 (R.complexTerm (n+4)) = 0
  exact (isZero_zero A.RightModule).eq_of_src _ _

noncomputable def finiteProjectiveCochainComplex : CochainComplex A.RightFiniteProjective ℤ :=
  R.finiteProjectiveComplex.extend ComplexShape.embeddingDownNat

theorem finiteProjectiveCochainComplex_isZero_outside (i : ℤ) (hi : i < -3 ∨ 0 < i) :
    IsZero (R.finiteProjectiveCochainComplex.X i) := by
  by_cases hm : ∃ n : ℕ, ComplexShape.embeddingDownNat.f n = i
  · obtain ⟨n,hn⟩ := hm
    have hn4 : 4 ≤ n := by dsimp [ComplexShape.embeddingDownNat] at hn; omega
    obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hn4
    rw [Nat.add_comm 4 m] at hn
    exact (R.finiteProjectiveComplex_isZero_ge_four m).of_iso
      (R.finiteProjectiveComplex.extendXIso ComplexShape.embeddingDownNat hn)
  · exact R.finiteProjectiveComplex.isZero_extend_X _ i (fun n hn => hm ⟨n,hn⟩)

noncomputable def boundedFiniteProjectiveCochainObject :
    ASGinzburg.BoundedHomotopyCategory A.RightFiniteProjective (ComplexShape.up ℤ) :=
  ⟨(HomotopyCategory.quotient _ _).obj R.finiteProjectiveCochainComplex,
    ⟨-3,0,R.finiteProjectiveCochainComplex_isZero_outside⟩⟩
end ASGinzburg.ZAlgebra.ASResolution
