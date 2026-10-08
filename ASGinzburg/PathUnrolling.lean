import ASGinzburg.UnrolledPathFiniteness
import ASGinzburg.PathWordEmbeddings

/-! Lifting genuine paths to the unrolled quiver with their actual cut
degree recorded in the terminal sheet. -/
namespace ASGinzburg.CutQuiver
variable {Q : CutQuiver}

def Path.transport {u v u' v' : Q.Vertex} (hu : u=u') (hv : v=v')
    (p : Q.Path u v) : Q.Path u' v' := hu ▸ hv ▸ p

@[simp] theorem Path.length_transport {u v u' v' : Q.Vertex}
    (hu : u=u') (hv : v=v') (p : Q.Path u v) :
    (p.transport hu hv).length=p.length := by subst u' v'; rfl

@[simp] theorem Path.cutDegree_transport {u v u' v' : Q.Vertex}
    (hu : u=u') (hv : v=v') (p : Q.Path u v) :
    (p.transport hu hv).cutDegree=p.cutDegree := by subst u' v'; rfl

@[simp] theorem Path.toList_transport {u v u' v' : Q.Vertex}
    (hu : u=u') (hv : v=v') (p : Q.Path u v) :
    (p.transport hu hv).toList=p.toList := by subst u' v'; rfl

def UnrolledPath.transport {u v u' v' : Q.LiftVertex} (hu : u=u') (hv : v=v')
    (p : Q.UnrolledPath u v) : Q.UnrolledPath u' v' := hu ▸ hv ▸ p

@[simp] theorem UnrolledPath.length_transport {u v u' v' : Q.LiftVertex}
    (hu : u=u') (hv : v=v') (p : Q.UnrolledPath u v) :
    (p.transport hu hv).length=p.length := by subst u' v'; rfl

def UnrolledPath.erase : {u v : Q.LiftVertex} → Q.UnrolledPath u v → Q.Path u.1 v.1
  | _,_,.nil v => .nil v.1
  | _,_,.snoc a p => (Path.snoc (erase p) a.val rfl).transport rfl a.property

@[simp] theorem UnrolledPath.erase_transport {u v u' v' : Q.LiftVertex}
    (hu : u=u') (hv : v=v') (p : Q.UnrolledPath u v) :
    (p.transport hu hv).erase=p.erase.transport (congrArg Prod.fst hu) (congrArg Prod.fst hv) := by
  subst u' v'
  rfl

theorem UnrolledPath.erase_length {u v : Q.LiftVertex} (p : Q.UnrolledPath u v) :
    p.erase.length=p.length := by
  induction p with
  | nil => simp [erase,Path.length,UnrolledPath.length]
  | snoc a p ih => simp [erase,Path.length,UnrolledPath.length,ih]

theorem UnrolledPath.erase_cutDegree {u v : Q.LiftVertex} (p : Q.UnrolledPath u v) :
    (p.erase.cutDegree : ℤ)=v.2-u.2 := by
  induction p with
  | nil => simp [erase,Path.cutDegree]
  | @snoc v a p ih =>
    simp only [erase,Path.cutDegree_transport,Path.cutDegree,Nat.cast_add,ih]
    dsimp [incomingSource,liftedSource]
    ring

theorem incomingSource_unroll (m : ℤ) {u v : Q.Vertex} (p : Q.Path u v)
    (a : Q.Arrow) (ha : Q.source a=v) :
    Q.incomingSource (Q.target a,m+(p.cutDegree:ℤ)+Q.cutDegree a) ⟨a,rfl⟩ =
      (v,m+(p.cutDegree:ℤ)) := by
  apply Prod.ext
  · exact ha
  · simp [incomingSource,liftedSource]

def Path.unroll (m : ℤ) : {u v : Q.Vertex} → (p : Q.Path u v) →
    Q.UnrolledPath (u,m) (v,m+(p.cutDegree:ℤ))
  | _,_,.nil u => (UnrolledPath.nil (u,m)).transport rfl (by simp [Path.cutDegree])
  | _,_,.snoc p a ha =>
    (UnrolledPath.snoc (v:=(Q.target a,m+(p.cutDegree:ℤ)+Q.cutDegree a)) ⟨a,rfl⟩
      ((unroll m p).transport rfl (incomingSource_unroll m p a ha).symm)).transport
        rfl (by simp [Path.cutDegree,Nat.cast_add,add_assoc])

theorem Path.unroll_length (m : ℤ) {u v : Q.Vertex} (p : Q.Path u v) :
    (p.unroll m).length=p.length := by
  induction p with
  | nil => simp [unroll,Path.length,UnrolledPath.length]
  | snoc p a ha ih => simp [unroll,Path.length,UnrolledPath.length,ih]

theorem Path.unroll_erase_toList (m : ℤ) {u v : Q.Vertex} (p : Q.Path u v) :
    (p.unroll m).erase.toList=p.toList := by
  induction p with
  | nil => simp [unroll,UnrolledPath.erase,Path.toList]
  | snoc p a ha ih => simp [unroll,UnrolledPath.erase,Path.toList,ih]

theorem Path.unroll_sigma_injective (m : ℤ) (u v : Q.Vertex) :
    Function.Injective (fun p : Q.Path u v =>
      (⟨(v,m+(p.cutDegree:ℤ)),p.unroll m⟩ : Σ w, Q.UnrolledPath (u,m) w)) := by
  intro p q h
  have H := congrArg (fun x : Σ w, Q.UnrolledPath (u,m) w => x.2.erase.toList) h
  simp only [Path.unroll_erase_toList] at H
  exact Path.toList_injective u v H

end ASGinzburg.CutQuiver
