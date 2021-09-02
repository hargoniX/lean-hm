import Lean

def Set (α : Type u) := α → Prop
def Set.in (s : Set α) (a : α) := s a

namespace Set

notation:50 a " ∈ " s:50 => Set.in s a

def pred (p : α → Prop) : Set α := p

notation "{" a "|" p "}" => Set.pred (fun a => p)

def union (s₁ s₂ : Set α) : Set α :=
  { a | a ∈ s₁ ∨ a ∈ s₂ }

infix:65 " ∪ " => Set.union

def inter (s₁ s₂ : Set α) : Set α :=
  { a | a ∈ s₁ ∧ a ∈ s₂ }

infix:70 " ∩ " => Set.inter

def subseteq (s₁ s₂ : Set α) : Prop :=
  ∀ a, a ∈ s₁ → a ∈ s₂

infix:75 " ⊆ " => Set.subseteq

def empty : Set α := fun x => False

notation (priority := high) "∅" => empty

theorem setext {A B : Set α} (h : ∀ x, x ∈ A ↔ x ∈ B) : A = B :=
  funext (fun x => propext (h x))

theorem inter_self (A : Set α) : A ∩ A = A :=
  setext fun x => Iff.intro
    (fun ⟨h, _⟩ => h)
    (fun h => ⟨h, h⟩)

theorem inter_empty (A : Set α) : A ∩ ∅ = ∅ :=
  setext fun x => Iff.intro
    (fun ⟨_, h⟩ => h)
    (fun h => False.elim h)

theorem empty_inter (A : Set α) : ∅ ∩ A = ∅ :=
  setext fun x => Iff.intro
    (fun ⟨h, _⟩ => h)
    (fun h => False.elim h)

theorem inter.comm (A B : Set α) : A ∩ B = B ∩ A :=
  setext fun x => Iff.intro
    (fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩)
    (fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩)

theorem inter.right (A B : Set α) (h1: x ∈ A) (h2: x ∈ B): ∀ x, x ∈ A ∧ x ∈ B → x ∈ B := by
  intro x xiab
  apply And.right
  case self =>
    apply xiab

theorem inter.left (A B : Set α) (h1: x ∈ A) (h2: x ∈ B): ∀ x, x ∈ A ∧ x ∈ B → x ∈ A := by
  intro a xiab
  apply And.left
  case self =>
    apply xiab

theorem inter.keep (A B : Set α) : ∀ x, x ∈ A → x ∈ B → x ∈ A := by
  intro a b c
  exact b

theorem inter.and {A B : Set α} {x : α} : x ∈ A → x ∈ B → x ∈ A ∧ x ∈ B := by
  intro a b
  exact And.intro a b

theorem inter.all_and (A B : Set α) : ∀ x, x ∈ A → x ∈ B → x ∈ A ∧ x ∈ B := by
  intro a
  exact And.intro

-- TODO why can't theorems be used as source for have := ?

end Set

-- Credits Henderik
theorem eq (A B : Set α) : (∀ x : α, x ∈ A ↔ x ∈ B) ↔ A = B := by
  apply Iff.intro
  case mp => 
    intro ablr
    funext x
    apply propext
    exact ablr x
  case mpr =>
    intro aeqb x
    rw [aeqb]
    exact Iff.refl _

theorem eqr (A B : Set α) :  A = B ↔ (∀ x : α, x ∈ A ↔ x ∈ B) := by
  apply Iff.symm
  apply eq

theorem subseteq {A B : Set α} : A ⊆ B ↔ A ∩ B = A := by
  apply Iff.intro
  case mp =>
    rw [eqr]
    intro seq x
    apply Iff.intro
    case mp =>
      have h : ∀ x, x ∈ A → x ∈ B := seq
      have h₁ : x ∈ A → x ∈ B := h x
      intro int
      have h₂ : x ∈ A ∧ x ∈ B := int
      have h₃ : x ∈ A := And.left h₂
      exact h₃
    case mpr =>
      intro xia
      have h : ∀ x, x ∈ A → x ∈ B := seq
      have h₁ : x ∈ A → x ∈ B := h x
      have h₂ : x ∈ B := h₁ xia
      have h₃ : x ∈ A ∧ x ∈ B := And.intro xia h₂
      exact h₃
  case mpr =>
    rw [eqr]
    intro xs x xia
    have h1 : x ∈ A ∧ x ∈ B ↔ x ∈ A := xs x
    have h2 : x ∈ A ∧ x ∈ B → x ∈ A := Iff.mp h1
    have h3 : x ∈ A ∧ x ∈ B := sorry -- TODO how to take the lhs of an implication into account?
    have h3 : x ∈ B := And.right h3
    exact h3
    