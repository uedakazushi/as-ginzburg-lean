import ASGinzburg.ASPathPresentation

/-! Local finiteness of the actual unrolled quiver's path sets follows from
strictly positive winding and finitely many incoming arrows. -/
namespace ASGinzburg.CutQuiver.UnrolledPath
variable {Q : CutQuiver}

def length {u v : Q.LiftVertex} : Q.UnrolledPath u v → ℕ
  | .nil _ => 0
  | .snoc _ p => length p + 1

theorem height_le {u v : Q.LiftVertex} (p : Q.UnrolledPath u v) :
    Q.height u ≤ Q.height v := by
  induction p with
  | nil => exact le_refl _
  | snoc a p ih =>
    have := Q.incomingSource_height_lt _ a
    omega

theorem height_lt_of_length_pos {u v : Q.LiftVertex} (p : Q.UnrolledPath u v)
    (hp : 0 < p.length) : Q.height u < Q.height v := by
  cases p with
  | nil => simp [length] at hp
  | snoc a p =>
    have := p.height_le
    have := Q.incomingSource_height_lt _ a
    omega

theorem diagonal_eq_nil {u : Q.LiftVertex} (p : Q.UnrolledPath u u) : p = .nil u := by
  cases p with
  | nil => rfl
  | snoc a p =>
    have := p.height_le
    have := Q.incomingSource_height_lt _ a
    omega

def lastStep : {u v : Q.LiftVertex} → Q.UnrolledPath u v →
    (PLift (u = v)) ⊕ (Σ a : Q.incomingArrows v, Q.UnrolledPath u (Q.incomingSource v a))
  | _, _, .nil _ => .inl ⟨rfl⟩
  | _, _, .snoc a p => .inr ⟨a,p⟩

theorem lastStep_injective {u v : Q.LiftVertex} :
    Function.Injective (lastStep (u := u) (v := v)) := by
  intro p q h
  cases p <;> cases q <;> simp only [lastStep] at h
  · rfl
  · cases h
  · cases h
  · cases h
    rfl

instance finite (u v : Q.LiftVertex) : Finite (Q.UnrolledPath u v) := by
  have hmain : ∀ d : ℕ, ∀ u v : Q.LiftVertex, (Q.height v - Q.height u).toNat = d →
      Finite (Q.UnrolledPath u v) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro u v hd
      by_cases hlt : Q.height v < Q.height u
      · haveI : IsEmpty (Q.UnrolledPath u v) := ⟨fun p => by have := p.height_le; omega⟩
        infer_instance
      by_cases heq : Q.height v=Q.height u
      · have hvu := Q.height_bijective.injective heq
        subst v
        haveI : Subsingleton (Q.UnrolledPath u u) :=
          ⟨fun p q => p.diagonal_eq_nil.trans q.diagonal_eq_nil.symm⟩
        infer_instance
      · haveI : ∀ a : Q.incomingArrows v, Finite (Q.UnrolledPath u (Q.incomingSource v a)) :=
          fun a => ih (Q.height (Q.incomingSource v a) - Q.height u).toNat
            (by have := Q.incomingSource_height_lt _ a; omega)
            u (Q.incomingSource v a) rfl
        exact Finite.of_injective lastStep lastStep_injective
  exact hmain (Q.height v - Q.height u).toNat u v rfl

end ASGinzburg.CutQuiver.UnrolledPath
