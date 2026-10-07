import ASGinzburg.CutPotential

/-!
# The actual linearized path algebra, component by component

`PathComponent u v` is the free k-vector space on directed paths u → v.
Multiplication has the order specified in the source: comp g f = g f.
Both associativity and the local-unit laws are proved, not postulated.
-/

namespace ASGinzburg.CutQuiver

universe u

namespace Path

variable {Q : CutQuiver}

def comp {u v w : Q.Vertex} (p : Q.Path u v) : Q.Path v w → Q.Path u w
  | .nil _ => p
  | .snoc q a h => .snoc (comp p q) a h

@[simp] theorem comp_nil {u v : Q.Vertex} (p : Q.Path u v) : p.comp (.nil v) = p := rfl

@[simp] theorem nil_comp {u v : Q.Vertex} (p : Q.Path u v) : (Path.nil u).comp p = p := by
  induction p with
  | nil => rfl
  | snoc p a h ih => simp [comp, ih]

theorem comp_assoc {u v w x : Q.Vertex} (p : Q.Path u v) (q : Q.Path v w)
    (r : Q.Path w x) : (p.comp q).comp r = p.comp (q.comp r) := by
  induction r with
  | nil => rfl
  | snoc r a h ih => simp [comp, ih]

theorem cutDegree_comp {u v w : Q.Vertex} (p : Q.Path u v) (q : Q.Path v w) :
    (p.comp q).cutDegree = p.cutDegree + q.cutDegree := by
  induction q with
  | nil => simp [comp, cutDegree]
  | snoc q a h ih => simp [comp, cutDegree, ih, Nat.add_assoc]

theorem winding_comp {u v w : Q.Vertex} (p : Q.Path u v) (q : Q.Path v w) :
    (p.comp q).winding = p.winding + q.winding := by
  induction q with
  | nil => simp [comp, winding]
  | snoc q a h ih => simp [comp, winding, ih, add_assoc]

end Path

variable (Q : CutQuiver) (k : Type u) [Field k]

abbrev PathComponent (u v : Q.Vertex) := Q.Path u v →₀ k

noncomputable def pathComp {u v w : Q.Vertex} :
    Q.PathComponent k v w →ₗ[k] Q.PathComponent k u v →ₗ[k] Q.PathComponent k u w :=
  Finsupp.linearCombination k (fun q =>
    Finsupp.linearCombination k (fun p => Finsupp.single (p.comp q) 1))

noncomputable def pathId (v : Q.Vertex) : Q.PathComponent k v v :=
  Finsupp.single (.nil v) 1

@[simp] theorem pathComp_single {u v w : Q.Vertex} (p : Q.Path u v) (q : Q.Path v w)
    (a b : k) : Q.pathComp k (Finsupp.single q b) (Finsupp.single p a) =
      Finsupp.single (p.comp q) (b * a) := by
  simp [pathComp, LinearMap.smul_apply, Finsupp.smul_single, smul_eq_mul]

theorem pathComp_id {u v : Q.Vertex} (f : Q.PathComponent k u v) :
    Q.pathComp k (Q.pathId k v) f = f := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g ihf ihg => simp [map_add, ihf, ihg]
  | single p a => simp [pathId]

theorem id_pathComp {u v : Q.Vertex} (f : Q.PathComponent k u v) :
    Q.pathComp k f (Q.pathId k u) = f := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g ihf ihg => simp [map_add, LinearMap.add_apply, ihf, ihg]
  | single p a => simp [pathId]

theorem pathComp_assoc {u v w x : Q.Vertex}
    (f : Q.PathComponent k u v) (g : Q.PathComponent k v w) (h : Q.PathComponent k w x) :
    Q.pathComp k h (Q.pathComp k g f) = Q.pathComp k (Q.pathComp k h g) f := by
  classical
  induction h using Finsupp.induction_linear with
  | zero => simp
  | add h h' ih ih' => simp [map_add, LinearMap.add_apply, ih, ih']
  | single r c =>
    induction g using Finsupp.induction_linear with
    | zero => simp
    | add g g' ih ih' => simp [map_add, ih, ih']
    | single q b =>
      induction f using Finsupp.induction_linear with
      | zero => simp
      | add f f' ih ih' => simp [map_add, LinearMap.add_apply, ih, ih']
      | single p a => simp [Path.comp_assoc, mul_assoc]

end ASGinzburg.CutQuiver
