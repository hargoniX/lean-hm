import Hm.Set

open Set

/-
Technically speaking relations also require a carrier set + a proof
that they are ⊆ carrier. However most applications we will every see
don't really care about the carrier set and just assume it to be
univ α β. Since always working with teh carrier set + proof in a structure
would clutter the implementation unnecessarily we will leave it out here.
-/
def Relation (α : Type u) (β : Type v) := Set (α × β)
def RelationOn (α : Type u) := Relation α α

instance FunctionToRelation : Coe (α → β → Prop) (Relation α β) where
  coe f := {t | f t.fst t.snd}

instance FunctionToRelationOn : Coe (α → α → Prop) (RelationOn α) where
  coe f := {t | f t.fst t.snd}

section RelationProperties


variable {α : Type _} (R : RelationOn α)

def reflexive := ∀ a : α, (a, a) ∈ R
def irreflexive := ∀ a : α, (a, a) ∉ R
def symmetrical := ∀ (a b : α), (a, b) ∈ R → (b, a) ∈ R
def transitive := ∀ (a b c : α), (a, b) ∈ R ∧ (b, c) ∈ R → (a, c) ∈ R
def antisymmetrical := ∀ (a b : α),  (a, b) ∈ R ∧ (b, a) ∈ R → a = b
def asymmetrical := ∀ (a b : α), (a, b) ∈ R → (b, a) ∉ R

class EquivalenceRel {α : Type _} (rel : RelationOn α) where
  reflexive : reflexive rel
  symmetrical : symmetrical rel
  transitive : transitive rel
  
/-
This instance allows us to use ≈ (denoted with \~~) when we know there
exists an equivalence relation on α.
variable (α : Type u) (a b : α) (R : RelationOn α) [EquivalenceRel R]
#check a ≈ b
-/
instance {rel : RelationOn α} [EquivalenceRel rel] : HasEquiv α where
  Equiv := λ a b => (a, b) ∈ rel

def equivalence_class {α : Type u} (R : RelationOn α) [EquivalenceRel R] (a : α) : Set α := {x | (a, x) ∈ R}
def id_rel (α : Type u) : RelationOn α := { t | t.fst = t.snd }

theorem id_rel_reflexive (α : Type u) : reflexive $ id_rel α := λ _ => rfl
  
end RelationProperties

-- Thanks to the coercion above we can now denote theorems such as
example : reflexive (Nat.le : RelationOn Nat) := by
  intro _
  exact Nat.le.refl

namespace Relation

variable (R: Relation α β) (S : Relation β γ)

def inverse : Relation β α := {t | (t.snd, t.fst) ∈ R}

postfix:max "⁻¹" => inverse

def comp : Relation α γ := { t | ∃ a, (t.fst, a) ∈ R ∧ (a, t.snd) ∈ S}

infixr:60 "∘" => comp

end Relation
