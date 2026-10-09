import Mathlib.Algebra.Homology.ConcreteCategory
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! Actual cycle classes and the concrete representative formula for
mathlib's connecting homomorphism in module cochain complexes. -/
namespace ASGinzburg
open CategoryTheory
universe u
variable {k : Type u} [Field k]

noncomputable def moduleCochainHomologyClass (K : CochainComplex (ModuleCat.{u} k) ℤ)
    (i : ℤ) (x : K.X i) (hx : K.d i (i+1) x=0) : K.homology i :=
  K.homologyπ i (K.cyclesMk x (i+1) (by simp) hx)

theorem moduleCochainHomologyClass_exists (K : CochainComplex (ModuleCat.{u} k) ℤ)
    (i : ℤ) (y : K.homology i) :
    ∃ x : K.X i, ∃ hx : K.d i (i+1) x=0,
      moduleCochainHomologyClass K i x hx=y := by
  obtain ⟨z,hz⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ i)).mp inferInstance y
  let x := K.iCycles i z
  have hx : K.d i (i+1) x=0 := congrArg (fun f => f z) (K.iCycles_d i (i+1))
  have he : K.cyclesMk x (i+1) (by simp) hx=z := by
    apply (ModuleCat.mono_iff_injective (K.iCycles i)).mp inferInstance
    exact K.i_cyclesMk (i:=i) x (i+1) (by simp) hx
  exact ⟨x,hx,by rw [moduleCochainHomologyClass,he,hz]⟩

theorem moduleCochainHomologyClass_naturality
    {K L : CochainComplex (ModuleCat.{u} k) ℤ} (f : K ⟶ L)
    (i : ℤ) (x : K.X i) (hx : K.d i (i+1) x=0)
    (hfx : L.d i (i+1) (f.f i x)=0) :
    HomologicalComplex.homologyMap f i (moduleCochainHomologyClass K i x hx)=
      moduleCochainHomologyClass L i (f.f i x) hfx := by
  have he : HomologicalComplex.cyclesMap f i (K.cyclesMk x (i+1) (by simp) hx)=
      L.cyclesMk (f.f i x) (i+1) (by simp) hfx := by
    apply (ModuleCat.mono_iff_injective (L.iCycles i)).mp inferInstance
    change (HomologicalComplex.cyclesMap f i ≫ L.iCycles i)
      (K.cyclesMk x (i+1) (by simp) hx)=_
    rw [HomologicalComplex.cyclesMap_i]
    change f.f i (K.iCycles i (K.cyclesMk x (i+1) (by simp) hx))=_
    have hi : K.iCycles i (K.cyclesMk x (i+1) (by simp) hx)=x := by
      change ((forget₂ (ModuleCat k) Ab).map (K.iCycles i))
        (K.cyclesMk x (i+1) (by simp) hx)=x
      exact K.i_cyclesMk (i:=i) x (i+1) (by simp) hx
    rw [hi]
    exact (L.i_cyclesMk (i:=i) (f.f i x) (i+1) (by simp) hfx).symm
  change (K.homologyπ i ≫ HomologicalComplex.homologyMap f i)
    (K.cyclesMk x (i+1) (by simp) hx)=_
  rw [HomologicalComplex.homologyπ_naturality]
  change L.homologyπ i
    (HomologicalComplex.cyclesMap f i (K.cyclesMk x (i+1) (by simp) hx))=_
  rw [he]
  rfl

theorem moduleCochainConnecting_class
    {S : ShortComplex (CochainComplex (ModuleCat.{u} k) ℤ)}
    (hS : S.ShortExact) (i : ℤ)
    (x₃ : S.X₃.X i) (hx₃ : S.X₃.d i (i+1) x₃=0)
    (x₂ : S.X₂.X i) (hx₂ : S.g.f i x₂=x₃)
    (x₁ : S.X₁.X (i+1)) (hx₁ : S.f.f (i+1) x₁=S.X₂.d i (i+1) x₂) :
    hS.δ i (i+1) (by simp) (moduleCochainHomologyClass S.X₃ i x₃ hx₃)=
      moduleCochainHomologyClass S.X₁ (i+1) x₁
        (hS.d_eq_zero_of_f_eq_d_apply i (i+1) x₂ x₁ hx₁ (i+1+1)) := by
  exact hS.δ_apply i (i+1) (by simp) x₃ hx₃ x₂ hx₂ x₁ hx₁ (i+1+1) (by simp)

end ASGinzburg
