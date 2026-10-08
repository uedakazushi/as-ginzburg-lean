import ASGinzburg.HomologyAugmentation
import ASGinzburg.GinzburgCutHomologyZero
import ASGinzburg.GinzburgCutBounds
import ASGinzburg.GinzburgCutRegularity

/-! Canonical maps from the actual Ginzburg complex to the actual H-zero
and Jacobian quotient complexes. Regularity is exactly their acyclicity. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory CategoryTheory.Limits
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgCutCochainZero_outgoing (φ : Q.Potential k) (u v : Q.Vertex) (c : ℤ) :
    ((Q.ginzburgCutCochainComplex k φ u v c).sc 0).g=0 := by
  change (Q.ginzburgCutCochainComplex k φ u v c).d 0 ((ComplexShape.up ℤ).next 0)=0
  have hn : (ComplexShape.up ℤ).next 0=0+1 := by simp
  rw [hn,Q.ginzburgCutCochainComplex_d]
  apply ModuleCat.hom_ext
  exact Q.ginzburgCutGradedDifferential_zero k φ u v c

noncomputable def ginzburgCutHomologyAugmentation (φ : Q.Potential k) (u v : Q.Vertex) (c : ℤ) :
    Q.ginzburgCutCochainComplex k φ u v c ⟶
      (HomologicalComplex.single (ModuleCat k) (ComplexShape.up ℤ) 0).obj
        (Q.ginzburgCutHomology k φ u v c 0) :=
  ASGinzburg.homologyAugmentation _ 0 (Q.ginzburgCutCochainZero_outgoing k φ u v c)

noncomputable def ginzburgCutJacobianAugmentation (φ : Q.Potential k) (u v : Q.Vertex) (c : ℤ) :
    Q.ginzburgCutCochainComplex k φ u v c ⟶
      (HomologicalComplex.single (ModuleCat k) (ComplexShape.up ℤ) 0).obj
        (ModuleCat.of k (Q.pathCutComponent k u v c ⧸ Q.pathJacobianCutIdeal k φ u v c)) :=
  Q.ginzburgCutHomologyAugmentation k φ u v c ≫
    (HomologicalComplex.single (ModuleCat k) (ComplexShape.up ℤ) 0).map
      (Q.ginzburgCutHomologyZeroJacobianIso k φ u v c).hom

theorem ginzburgCutHomologyAugmentation_quasiIso_iff (φ : Q.Potential k) (u v : Q.Vertex) (c : ℤ) :
    QuasiIso (Q.ginzburgCutHomologyAugmentation k φ u v c) ↔
      ∀ q : ℤ, q<0 → IsZero (Q.ginzburgCutHomology k φ u v c q) := by
  rw [ginzburgCutHomologyAugmentation,ASGinzburg.homologyAugmentation_quasiIso_iff]
  constructor
  · intro h q hq
    exact h q (by omega)
  · intro h q hq
    by_cases hn : q<0
    · exact h q hn
    · exact Q.ginzburgCutHomology_isZero_of_outside k φ u v c q (Or.inr (by omega))

theorem ginzburgCutJacobianAugmentation_quasiIso_iff (φ : Q.Potential k) (u v : Q.Vertex) (c : ℤ) :
    QuasiIso (Q.ginzburgCutJacobianAugmentation k φ u v c) ↔
      ∀ q : ℤ, q<0 → IsZero (Q.ginzburgCutHomology k φ u v c q) := by
  rw [ginzburgCutJacobianAugmentation,quasiIso_iff_comp_right]
  exact Q.ginzburgCutHomologyAugmentation_quasiIso_iff k φ u v c

theorem ginzburgRegular_iff_cutAugmentation_quasiIso (φ : Q.Potential k) :
    Q.GinzburgRegular k φ ↔ ∀ u v : Q.Vertex, ∀ c : ℤ,
      QuasiIso (Q.ginzburgCutJacobianAugmentation k φ u v c) := by
  rw [Q.ginzburgRegular_iff_cutHomology]
  simp only [Q.ginzburgCutJacobianAugmentation_quasiIso_iff]

end ASGinzburg.CutQuiver
