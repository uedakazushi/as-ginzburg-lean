import ASGinzburg.GinzburgGeneratorGradings
import Mathlib.Data.Fintype.Vector
import Mathlib.LinearAlgebra.Dimension.Finite

/-! Positive winding bounds the length of extended paths. Thus every
fixed internal degree path space is genuinely finite dimensional. -/
namespace ASGinzburg.CutQuiver
variable (Q : CutQuiver)

def GinzburgArrow.finiteCode : Q.GinzburgArrow → (Q.Arrow⊕Q.Arrow)⊕Q.Vertex
  | .original a => .inl (.inl a)
  | .dual a => .inl (.inr a)
  | .loop v => .inr v

theorem GinzburgArrow.finiteCode_injective : Function.Injective (GinzburgArrow.finiteCode Q) := by
  intro a b h
  cases a <;> cases b <;> simp [finiteCode] at h
  all_goals cases h; rfl

instance GinzburgArrow.finite : Finite Q.GinzburgArrow :=
  Finite.of_injective (GinzburgArrow.finiteCode Q) (GinzburgArrow.finiteCode_injective Q)

theorem GinzburgPath.length_le_winding {u v : Q.Vertex} (p : Q.GinzburgPath u v) :
    (p.length:ℤ)≤p.winding := by
  induction p with
  | nil => simp [length,winding]
  | snoc p a h ih =>
    have := a.winding_pos Q
    simp only [length,winding,Nat.cast_add,Nat.cast_one]
    omega

noncomputable def GinzburgPath.boundedWord {u v : Q.Vertex} (w : ℤ)
    (p : {p : Q.GinzburgPath u v // p.winding=w}) :
    Σ n : Fin (w.toNat+1), List.Vector Q.GinzburgArrow n.val :=
  ⟨⟨p.val.length,by
    have hlen := p.val.length_le_winding Q
    have hw := p.val.winding_nonneg
    rw [p.property] at hlen hw
    omega⟩,⟨p.val.toList,p.val.length_toList⟩⟩

theorem GinzburgPath.boundedWord_injective {u v : Q.Vertex} (w : ℤ) :
    Function.Injective (GinzburgPath.boundedWord Q (u:=u) (v:=v) w) := by
  intro p q h
  have hw := congrArg (fun z : Σ n : Fin (w.toNat+1), List.Vector Q.GinzburgArrow n.val => z.2.val) h
  apply Subtype.ext
  exact GinzburgPath.toList_injective u v hw

instance GinzburgPath.finiteFixedWinding (u v : Q.Vertex) (w : ℤ) :
    Finite {p : Q.GinzburgPath u v // p.winding=w} := by
  letI := Fintype.ofFinite Q.GinzburgArrow
  exact Finite.of_injective (GinzburgPath.boundedWord Q w) (GinzburgPath.boundedWord_injective Q w)

instance GinzburgPath.finiteFixedCut (u v : Q.Vertex) (c : ℤ) :
    Finite {p : Q.GinzburgPath u v // p.cutDegree=c} := by
  let f : {p : Q.GinzburgPath u v // p.cutDegree=c} →
      {p : Q.GinzburgPath u v // p.winding=(v.val:ℤ)-u.val+Q.vertices*c} :=
    fun p => ⟨p.val,by rw [p.val.winding_formula,p.property]⟩
  apply Finite.of_injective f
  intro p q h
  apply Subtype.ext
  exact congrArg (fun z : {p : Q.GinzburgPath u v //
    p.winding=(v.val:ℤ)-u.val+Q.vertices*c} => z.val) h

universe u
variable (k : Type u) [Field k]

instance ginzburgCutComponent_finite (u v : Q.Vertex) (c : ℤ) :
    Module.Finite k (Q.ginzburgCutComponent k u v c) := by
  let S : Set (Q.GinzburgPath u v) := {p | p.cutDegree=c}
  haveI : Finite S := by
    change Finite {p : Q.GinzburgPath u v // p.cutDegree=c}
    infer_instance
  letI : Fintype S := Fintype.ofFinite S
  let e : Q.ginzburgCutComponent k u v c ≃ₗ[k] (S →₀ k) :=
    Finsupp.supportedEquivFinsupp (M:=k) (R:=k) S
  exact Module.Finite.equiv e.symm

end ASGinzburg.CutQuiver
