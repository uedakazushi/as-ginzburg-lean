import ASGinzburg.FiniteVertexFiltration
import ASGinzburg.ASLeftExtReciprocity

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

theorem rightVertexFiltration_ext_other_eq_zero (hAS : A.ASRegular Q)
    {M : A.RightModule} (F : A.RightVertexFiltration M) (i : ℤ) (n : ℕ)
    (hn : n ≠ 3) (e : Abelian.Ext.{v} M (A.representable i) n) : e = 0 := by
  induction F with
  | zero hM =>
    rw [← e.mk₀_id_comp, hM.eq_of_src (𝟙 _) 0, Abelian.Ext.mk₀_zero,
      Abelian.Ext.zero_comp]
  | @step M j f hf tail ih =>
    letI := hf
    let S : ShortComplex A.RightModule :=
      ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel f }
    have hz : (Abelian.Ext.mk₀ S.f).comp e (zero_add n) = 0 := by
      have hall : ∀ x : Abelian.Ext.{v} (A.simpleRightModule j) (A.representable i) n,
          x = 0 := by
        obtain ⟨a, rfl⟩ := Q.height_bijective.surjective i
        obtain ⟨b, rfl⟩ := Q.height_bijective.surjective j
        exact hAS.ext_other_eq_zero A Q a b n (fun h => hn (Prod.mk.inj h).1)
      exact hall _
    obtain ⟨x,hx⟩ := Abelian.Ext.contravariant_sequence_exact₂ hS (A.representable i) e hz
    rw [← hx, ih x, Abelian.Ext.comp_zero]

theorem rightFiniteDimensional_ext_other_eq_zero (hAS : A.ASRegular Q)
    (M : A.RightModule) (hM : A.rightFiniteDimensionalProperty M)
    (i : ℤ) (n : ℕ) (hn : n ≠ 3)
    (e : Abelian.Ext.{v} M (A.representable i) n) : e = 0 :=
  A.rightVertexFiltration_ext_other_eq_zero Q hAS
    (A.rightFiniteDimensionalVertexFiltration M hM) i n hn e
end ASGinzburg.ZAlgebra

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

theorem leftVertexFiltration_ext_other_eq_zero (hAS : A.ASRegular Q)
    {M : A.LeftModule} (F : A.LeftVertexFiltration M) (i : ℤ) (n : ℕ)
    (hn : n ≠ 3) (e : Abelian.Ext.{v} M (A.leftRepresentable i) n) : e = 0 := by
  induction F with
  | zero hM =>
    rw [← e.mk₀_id_comp, hM.eq_of_src (𝟙 _) 0, Abelian.Ext.mk₀_zero,
      Abelian.Ext.zero_comp]
  | @step M j f hf tail ih =>
    letI := hf
    let S : ShortComplex A.LeftModule :=
      ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel f }
    have hz : (Abelian.Ext.mk₀ S.f).comp e (zero_add n) = 0 := by
      have hall : ∀ x : Abelian.Ext.{v} (A.simpleLeftModule j) (A.leftRepresentable i) n,
          x = 0 := by
        obtain ⟨b, rfl⟩ := Q.height_bijective.surjective j
        exact hAS.leftExt_other_eq_zero A Q b i n hn
      exact hall _
    obtain ⟨x,hx⟩ := Abelian.Ext.contravariant_sequence_exact₂ hS (A.leftRepresentable i) e hz
    rw [← hx, ih x, Abelian.Ext.comp_zero]

theorem leftFiniteDimensional_ext_other_eq_zero (hAS : A.ASRegular Q)
    (M : A.LeftModule) (hM : A.leftFiniteDimensionalProperty M)
    (i : ℤ) (n : ℕ) (hn : n ≠ 3)
    (e : Abelian.Ext.{v} M (A.leftRepresentable i) n) : e = 0 :=
  A.leftVertexFiltration_ext_other_eq_zero Q hAS
    (A.leftFiniteDimensionalVertexFiltration M hM) i n hn e
end ASGinzburg.ZAlgebra
