import Hm.Set

open Set

/-
Technically speaking relations also require a carrier set + a proof
that they are ⊆ carrier. However most applications we will every see
don't really care about the carrier set and just assume it to be
univ (α × β). Since always working with the carrier set + proof in a structure
would clutter the implementation unnecessarily.
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

class EquivalenceRel {α : Type _} (R : RelationOn α) where
  reflexive : reflexive R
  symmetrical : symmetrical R
  transitive : transitive R

/-
This instance allows us to use ≈ (denoted with \~~) when we know there
exists an equivalence relation on α.
variable (α : Type u) (a b : α) (R : RelationOn α) [EquivalenceRel R]
#check a ≈ b
-/
instance {R : RelationOn α} [EquivalenceRel R] : HasEquiv α where
  Equiv := λ a b => (a, b) ∈ R

def equivalence_class (R : RelationOn α) [EquivalenceRel R] (a : α) : Set α := {x | a ≈ x }

theorem equivalence_classes_disjunct (R: RelationOn α) [eqr: EquivalenceRel R] (a b : α) (a_nequiv_b: ¬(a ≈ b)) : equivalence_class R a ∩ equivalence_class R b = ∅ := by
  apply eq_empty_iff_all_notin.mpr
  intro x hx
  have a_equiv_x : a ≈ x := hx.left
  have b_equiv_x : b ≈ x := hx.right
  have x_equiv_b : x ≈ b := eqr.symmetrical b x b_equiv_x
  have a_equiv_b : a ≈ b := eqr.transitive a x b ⟨a_equiv_x, x_equiv_b⟩
  exact a_nequiv_b a_equiv_b

def id_rel (α : Type u) : RelationOn α := { t | t.fst = t.snd }

theorem mem_id_rel (a b : α) : (a, b) ∈ id_rel α ↔ a = b := Iff.rfl

theorem id_rel_reflexive (α : Type u) : reflexive $ id_rel α := λ _ => rfl
  
end RelationProperties

-- Thanks to the coercion above we can now denote theorems such as
example : reflexive (Nat.le : RelationOn Nat) := λ _ => Nat.le.refl

namespace Relation

def inverse (R : Relation α β) : Relation β α := {t | (t.snd, t.fst) ∈ R}

postfix:max "⁻¹" => inverse

def comp (R : Relation α β) (S : Relation β γ) : Relation α γ := { t | ∃ a, (t.fst, a) ∈ R ∧ (a, t.snd) ∈ S}

infixr:60 "∘" => comp

section usability

theorem mem_inverse (R : Relation α β) : x ∈ R⁻¹ ↔ (x.snd, x.fst) ∈ R := Iff.rfl

theorem mem_comp (x : α × γ) (R : Relation α β) (S : Relation β γ) : (x ∈ R∘S) ↔ (∃ a, (x.fst, a) ∈ R ∧ (a, x.snd) ∈ S) := ⟨id, id⟩

theorem mem_comp_of_left_right (a : β) (x : α × γ) (R : Relation α β) (S : Relation β γ) : (x.fst, a) ∈ R → (a, x.snd) ∈ S → x ∈ R ∘ S := by
  intro hr hs
  exact Exists.intro a $ And.intro hr hs

end usability

theorem comp_inverse_distrib {R₁ R₂: RelationOn α} : (R₁∘R₂)⁻¹ = R₂⁻¹∘R₁⁻¹ := by
  apply setext
  intro x
  apply Iff.intro <;>
  {
    intro h;
    cases h with
    | intro y h₂ =>
      exact Exists.intro y ⟨h₂.right, h₂.left⟩
  }

-- Alternative proof that shows steps in more detail
example {R₁ R₂: RelationOn α} : (R₁∘R₂)⁻¹ = R₂⁻¹∘R₁⁻¹ := by
  apply setext
  intro x
  apply Iff.intro
  case h.mp =>
    intro h
    rw [mem_inverse, mem_comp] at h
    simp at h
    apply Exists.elim h
    intro a ha
    apply mem_comp_of_left_right a x
    case a =>
      rw [mem_inverse]
      simp
      exact ha.right
    case a =>
      rw [mem_inverse]
      simp
      exact ha.left
  case h.mpr =>
    intro h
    rw [mem_inverse, mem_comp]
    simp
    rw [mem_comp] at h
    apply Exists.elim h
    intro a ha
    rw [mem_inverse, mem_inverse] at ha
    simp at ha
    exists a
    exact And.intro ha.right ha.left

theorem rel_and_rel_impl_comp {R S : RelationOn α} {A B C : Set α} :
  R ⊆ (cartesian A B) ∧ S ⊆ (cartesian B C) → (R ∘ S) ⊆ (cartesian A C) := by
    intro h x comp
    rw [mem_comp] at comp
    apply Exists.elim comp
    intro a ha
    apply mem_cartesian_of_left_right x A C
    case a =>
      exact And.left $ h.left (x.fst, a) ha.left
    case a =>
      exact And.right $ h.right (a, x.snd) ha.right

end Relation
