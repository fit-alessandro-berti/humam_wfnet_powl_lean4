namespace KouraniWfnetPowl

abbrev Set (alpha : Sort u) := alpha -> Prop

namespace Set

instance : Membership alpha (Set alpha) where
  mem s x := s x

def empty : Set alpha := fun _ => False

def univ : Set alpha := fun _ => True

def singleton (x : alpha) : Set alpha := fun y => y = x

def inter (s t : Set alpha) : Set alpha := fun x => x ∈ s ∧ x ∈ t

def union (s t : Set alpha) : Set alpha := fun x => x ∈ s ∨ x ∈ t

def compl (s : Set alpha) : Set alpha := fun x => ¬ x ∈ s

def diff (s t : Set alpha) : Set alpha := fun x => x ∈ s ∧ ¬ x ∈ t

def subset (s t : Set alpha) : Prop := ∀ {x}, x ∈ s -> x ∈ t

theorem ext {s t : Set alpha} (h : ∀ x, x ∈ s ↔ x ∈ t) : s = t := by
  funext x
  exact propext (h x)

end Set

abbrev Rel (alpha : Sort u) := alpha -> alpha -> Prop

def Irreflexive (r : Rel alpha) : Prop := ∀ x, ¬ r x x

def Transitive (r : Rel alpha) : Prop :=
  ∀ {x y z}, r x y -> r y z -> r x z

def Asymmetric (r : Rel alpha) : Prop :=
  ∀ {x y}, r x y -> ¬ r y x

structure StrictPartialOrder (alpha : Sort u) where
  rel : Rel alpha
  irrefl : Irreflexive rel
  trans : Transitive rel

namespace StrictPartialOrder

theorem asymmetric (order : StrictPartialOrder alpha) : Asymmetric order.rel := by
  intro x y hxy hyx
  exact order.irrefl x (order.trans hxy hyx)

end StrictPartialOrder

theorem irreflexive_transitive_asymmetric
    {r : Rel alpha}
    (hirrefl : Irreflexive r)
    (htrans : Transitive r) :
    Asymmetric r := by
  intro x y hxy hyx
  exact hirrefl x (htrans hxy hyx)

inductive TransGen (r : Rel alpha) : Rel alpha where
  | single {x y : alpha} : r x y -> TransGen r x y
  | tail {x y z : alpha} : r x y -> TransGen r y z -> TransGen r x z

namespace TransGen

theorem trans {r : Rel alpha} : Transitive (TransGen r) := by
  intro x y z hxy hyz
  induction hxy generalizing z with
  | single h =>
      exact TransGen.tail h hyz
  | tail h _ ih =>
      exact TransGen.tail h (ih hyz)

theorem mono
    {r s : Rel alpha}
    (hrel : ∀ {x y}, r x y -> s x y) :
    ∀ {x y}, TransGen r x y -> TransGen s x y := by
  intro x y hpath
  induction hpath with
  | single h =>
      exact TransGen.single (hrel h)
  | tail h _ ih =>
      exact TransGen.tail (hrel h) ih

theorem congr
    {r s : Rel alpha}
    (hrel : ∀ x y, r x y ↔ s x y)
    {x y : alpha} :
    TransGen r x y ↔ TransGen s x y := by
  constructor
  · exact mono (fun {x y} h => (hrel x y).mp h)
  · exact mono (fun {x y} h => (hrel x y).mpr h)

theorem irrefl_of_no_return
    {r : Rel alpha}
    (hnoReturn : ∀ {x y}, r x y -> ¬ TransGen r y x) :
    Irreflexive (TransGen r) := by
  intro x hcycle
  cases hcycle with
  | single h =>
      exact hnoReturn h (TransGen.single h)
  | tail hxy hyx =>
      exact hnoReturn hxy hyx

theorem no_return_of_irrefl
    {r : Rel alpha}
    (hirrefl : Irreflexive (TransGen r)) :
    ∀ {x y}, r x y -> ¬ TransGen r y x := by
  intro x y hxy hyx
  exact hirrefl x (TransGen.tail hxy hyx)

theorem irrefl_iff_no_return
    {r : Rel alpha} :
    Irreflexive (TransGen r) ↔
      ∀ {x y}, r x y -> ¬ TransGen r y x :=
  ⟨no_return_of_irrefl, irrefl_of_no_return⟩

end TransGen

end KouraniWfnetPowl
