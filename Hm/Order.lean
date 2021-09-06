import Hm.Set
import Hm.Relation

class HasPrec (α : Sort u) where
  Prec : α → α → Sort v

export HasPrec (Prec)
  
class HasPrecEq (α : Sort u) where
  PrecEq : α → α → Sort v
  
export HasPrecEq (PrecEq)

infix:55 " ≺ " => HasPrec.Prec
infix:55 " ≼ " => HasPrecEq.PrecEq

class PartialOrder {α : Type _} (rel : RelationOn α) where
  reflexive : reflexive rel
  antisymmetrical : antisymmetrical rel
  transitive : transitive rel
  
class StrictPartialOrder {α : Type _} (rel : RelationOn α) where
  irreflexive : irreflexive rel
  asymmetrical : asymmetrical rel
  transitive : transitive rel

/-
These instances allow us to use ≺ and ≼ (denoted with \prec \preceq)
when we know there exist PartialOrder Relations on a type α

variable (α : Type u) (a b : α) (R : RelationOn α) [PartialOrder R]
#check a ≼ b

And

variable (α : Type u) (a b : α) (R : RelationOn α) [StrictPartialOrder R]
#check a ≺ b

However you have to be careful about this in the presence of multiple
PartialOrder / StrictPartialOrder relations at once since lean will
automatically pick one according to what it thinks is best. This might
however not be what you think is best
-/

instance {R : RelationOn α} [PartialOrder R] : HasPrecEq α where
  PrecEq := λ a b => (a, b) ∈ R

instance {R : RelationOn α} [StrictPartialOrder R] : HasPrec α where
  Prec := λ a b => (a, b) ∈ R

def comparable {α : Type u} (R : RelationOn α) [PartialOrder R] (a : α) (b : α) : Prop := a ≼ b ∨ b ≼ a

def strict_comparable {α : Type u} (R : RelationOn α) [StrictPartialOrder R] (a : α) (b : α) : Prop := a ≺ b ∨ b ≺ a

class TotalOrder {α : Type _} (rel : RelationOn α) extends PartialOrder rel where
  total : ∀ a b, comparable rel a b

class StrictTotalOrder {α : Type _} (rel : RelationOn α) extends StrictPartialOrder rel where
  total : ∀ a b, strict_comparable rel a b

namespace PartialOrder

def minimum (R : RelationOn α) [PartialOrder R] (x : α) : Prop := ¬(∃ y, y ≠ x ∧ y ≼ x)
def topoligical_sorting (TR : RelationOn α) [TotalOrder TR] (R : RelationOn α) [PartialOrder R] : Prop :=
  R ⊆ TR
  
inductive Chain {α : Type u} (R: RelationOn α) [PartialOrder R] : List α → Prop where
| single : Chain R [a]
| cons_cons (preceq: a ≼ b) (neq: a ≠ b) : Chain R (b :: l) → Chain R (a :: b :: l)

-- A Tactic that can do stuff like this automatically might be interesting
example [PartialOrder (Nat.le : RelationOn Nat)]: Chain (Nat.le : RelationOn Nat) [0, 1, 2] := by
  apply Chain.cons_cons
  case preceq =>
    exact Nat.le.step $ Nat.le.refl
  case neq =>
    intro h
    injection h
  case a =>
    apply Chain.cons_cons
    case preceq =>
      exact Nat.le.step $ Nat.le.refl
    case neq =>
      intro h
      injection h with h
      injection h
    case a =>
      exact Chain.single
end PartialOrder

namespace StrictPartialOrder


def minimum (R : RelationOn α) [StrictPartialOrder R] (x : α) : Prop := ¬(∃y, y ≠ x ∧ y ≺ x)
def topoligical_sorting (TR : RelationOn α) [StrictTotalOrder TR] (R : RelationOn α) [StrictPartialOrder R] : Prop :=
  R ⊆ TR

inductive Chain {α : Type u} (R: RelationOn α) [StrictPartialOrder R] : List α → Prop where
| single : Chain R [a]
| cons_cons (prec: a ≺ b) : Chain R (b :: l) → Chain R (a :: b :: l)

example [StrictPartialOrder (Nat.lt : RelationOn Nat)]: Chain (Nat.lt : RelationOn Nat) [0, 1, 2] := by
  apply Chain.cons_cons
  case prec =>
    exact Nat.lt.base 0
  case a =>
    apply Chain.cons_cons
    case prec =>
      exact Nat.lt.base 1
    case a =>
      exact Chain.single

end StrictPartialOrder

