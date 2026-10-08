import ASGinzburg.FiniteProjectiveClosure
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits
universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C] (P Q : C)
  [HasBinaryBiproduct P Q] [HasCoproduct (fun b : Bool => (match b with | false => Q | true => P))]

noncomputable def boolCoproductIsoBiprod : (∐ fun b : Bool => (match b with | false => Q | true => P)) ≅ P ⊞ Q where
  hom := Sigma.desc (fun b => match b with | false => biprod.inr | true => biprod.inl)
  inv := biprod.desc (Sigma.ι (fun b : Bool => (match b with | false => Q | true => P)) true)
    (Sigma.ι (fun b : Bool => (match b with | false => Q | true => P)) false)
  hom_inv_id := by
    apply Sigma.hom_ext
    intro b
    cases b <;> simp
  inv_hom_id := by
    apply biprod.hom_ext'
    · simp
    · simp
end ASGinzburg

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

theorem rightFiniteProjectiveProperty_of_retract {P Q : A.RightModule} (r : Retract P Q)
    (hQ : A.rightFiniteProjectiveProperty Q) : A.rightFiniteProjectiveProperty P := by
  obtain ⟨n,i,⟨rQ⟩⟩ := hQ
  exact ⟨n,i,⟨r.trans rQ⟩⟩

theorem rightFiniteProjectiveProperty_of_iso {P Q : A.RightModule} (e : P ≅ Q)
    (hQ : A.rightFiniteProjectiveProperty Q) : A.rightFiniteProjectiveProperty P :=
  A.rightFiniteProjectiveProperty_of_retract (Retract.ofIso e) hQ

theorem rightFiniteProjectiveProperty_finite_coproduct {B : Type*} [Fintype B]
    (P : B → A.RightModule) (hP : ∀ b, A.rightFiniteProjectiveProperty (P b)) :
    A.rightFiniteProjectiveProperty (∐ P) := by
  classical
  choose n i hr using hP
  let r : Retract (∐ P) (∐ fun b => ∐ fun j : Fin (n b) => A.representable (i b j)) :=
    { i := CategoryTheory.Limits.Sigma.map (fun b => (hr b).some.i)
      r := CategoryTheory.Limits.Sigma.map (fun b => (hr b).some.r)
      retract := by
        rw [CategoryTheory.Limits.Sigma.map_comp_map]
        simp only [Retract.retract,CategoryTheory.Limits.Sigma.map_id] }
  let e := sigmaSigmaIso (fun b => Fin (n b)) (fun b j => A.representable (i b j))
  apply A.rightFiniteProjectiveProperty_of_retract (r.trans (Retract.ofIso e))
  exact A.rightFiniteProjectiveProperty_coproduct (fun p : Σ b, Fin (n b) => i p.1 p.2)

theorem rightFiniteProjectiveProperty_biprod {P Q : A.RightModule}
    (hP : A.rightFiniteProjectiveProperty P) (hQ : A.rightFiniteProjectiveProperty Q) :
    A.rightFiniteProjectiveProperty (P ⊞ Q) := by
  apply A.rightFiniteProjectiveProperty_of_iso (ASGinzburg.boolCoproductIsoBiprod P Q).symm
  apply A.rightFiniteProjectiveProperty_finite_coproduct
  intro b
  cases b
  · exact hQ
  · exact hP

theorem rightFiniteProjectiveProperty_of_shortExact {S : ShortComplex A.RightModule}
    (hS : S.ShortExact) (h₁ : A.rightFiniteProjectiveProperty S.X₁)
    (h₃ : A.rightFiniteProjectiveProperty S.X₃) : A.rightFiniteProjectiveProperty S.X₂ := by
  letI : Projective S.X₃ := A.rightFiniteProjectiveProperty_projective h₃
  apply A.rightFiniteProjectiveProperty_of_iso hS.splittingOfProjective.isoBinaryBiproduct
  exact A.rightFiniteProjectiveProperty_biprod h₁ h₃
end ASGinzburg.ZAlgebra

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

theorem leftFiniteProjectiveProperty_of_retract {P Q : A.LeftModule} (r : Retract P Q)
    (hQ : A.leftFiniteProjectiveProperty Q) : A.leftFiniteProjectiveProperty P := by
  obtain ⟨n,i,⟨rQ⟩⟩ := hQ
  exact ⟨n,i,⟨r.trans rQ⟩⟩

theorem leftFiniteProjectiveProperty_of_iso {P Q : A.LeftModule} (e : P ≅ Q)
    (hQ : A.leftFiniteProjectiveProperty Q) : A.leftFiniteProjectiveProperty P :=
  A.leftFiniteProjectiveProperty_of_retract (Retract.ofIso e) hQ

theorem leftFiniteProjectiveProperty_finite_coproduct {B : Type*} [Fintype B]
    (P : B → A.LeftModule) (hP : ∀ b, A.leftFiniteProjectiveProperty (P b)) :
    A.leftFiniteProjectiveProperty (∐ P) := by
  classical
  choose n i hr using hP
  let r : Retract (∐ P) (∐ fun b => ∐ fun j : Fin (n b) => A.leftRepresentable (i b j)) :=
    { i := CategoryTheory.Limits.Sigma.map (fun b => (hr b).some.i)
      r := CategoryTheory.Limits.Sigma.map (fun b => (hr b).some.r)
      retract := by
        rw [CategoryTheory.Limits.Sigma.map_comp_map]
        simp only [Retract.retract,CategoryTheory.Limits.Sigma.map_id] }
  let e := sigmaSigmaIso (fun b => Fin (n b)) (fun b j => A.leftRepresentable (i b j))
  apply A.leftFiniteProjectiveProperty_of_retract (r.trans (Retract.ofIso e))
  exact A.leftFiniteProjectiveProperty_coproduct (fun p : Σ b, Fin (n b) => i p.1 p.2)

theorem leftFiniteProjectiveProperty_biprod {P Q : A.LeftModule}
    (hP : A.leftFiniteProjectiveProperty P) (hQ : A.leftFiniteProjectiveProperty Q) :
    A.leftFiniteProjectiveProperty (P ⊞ Q) := by
  apply A.leftFiniteProjectiveProperty_of_iso (ASGinzburg.boolCoproductIsoBiprod P Q).symm
  apply A.leftFiniteProjectiveProperty_finite_coproduct
  intro b
  cases b
  · exact hQ
  · exact hP

theorem leftFiniteProjectiveProperty_of_shortExact {S : ShortComplex A.LeftModule}
    (hS : S.ShortExact) (h₁ : A.leftFiniteProjectiveProperty S.X₁)
    (h₃ : A.leftFiniteProjectiveProperty S.X₃) : A.leftFiniteProjectiveProperty S.X₂ := by
  letI : Projective S.X₃ := A.leftFiniteProjectiveProperty_projective h₃
  apply A.leftFiniteProjectiveProperty_of_iso hS.splittingOfProjective.isoBinaryBiproduct
  exact A.leftFiniteProjectiveProperty_biprod h₁ h₃
end ASGinzburg.ZAlgebra
