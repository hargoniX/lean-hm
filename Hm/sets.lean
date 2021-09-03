import Lean

def Set (α : Type u) := α → Prop
def Set.in (s : Set α) (a : α) := s a

namespace Set

notation:50 a " ∈ " s:50 => Set.in s a

notation:55 a " ∉ " s:55 => ¬Set.in s a

def pred (p : α → Prop) : Set α := p

notation "{" a "|" p "}" => Set.pred (λ a => p)

def union (s₁ s₂ : Set α) : Set α :=
  { a | a ∈ s₁ ∨ a ∈ s₂ }

infix:65 " ∪ " => Set.union

def inter (s₁ s₂ : Set α) : Set α :=
  { a | a ∈ s₁ ∧ a ∈ s₂ }

infix:70 " ∩ " => Set.inter

def subseteq (s₁ s₂ : Set α) : Prop :=
  ∀ a, a ∈ s₁ → a ∈ s₂

infix:75 " ⊆ " => Set.subseteq

def comp (s₁ s₂ : Set α) : Set α :=
  { a | a ∈ s₁ ∧ a ∉ s₂ }

infix:80 " \\ " => Set.subseteq

def empty : Set α := λ x => False

notation (priority := high) "∅" => empty

theorem setext {A B : Set α} (h : ∀ x, x ∈ A ↔ x ∈ B) : A = B :=
  funext (λ x => propext (h x))

theorem inter_self (A : Set α) : A ∩ A = A :=
  setext λ x => Iff.intro
    (λ ⟨h, _⟩ => h)
    (λ h => ⟨h, h⟩)

theorem inter_empty (A : Set α) : A ∩ ∅ = ∅ :=
  setext λ x => Iff.intro
    (λ ⟨_, h⟩ => h)
    (λ h => False.elim h)

theorem empty_inter (A : Set α) : ∅ ∩ A = ∅ :=
  setext λ x => Iff.intro
    (λ ⟨h, _⟩ => h)
    (λ h => False.elim h)

theorem inter.comm (A B : Set α) : A ∩ B = B ∩ A :=
  setext λ x => Iff.intro
    (λ ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩)
    (λ ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩)

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

theorem sub_eq_cap {A B : Set α} : A ⊆ B ↔ A ∩ B = A := by
  apply Iff.intro
  case mp =>
    rw [eqr]
    intro seq x
    apply Iff.intro
    case mp =>
      intro xiab
      apply And.left xiab
    case mpr =>
      intro x₂
      have h : x ∈ B := (seq x) x₂
      exact And.intro x₂ h
  case mpr =>
    rw [eqr]
    intro xs x xia
    have h : x ∈ A ∩ B := Iff.mpr (xs x) xia
    exact And.right h

theorem sub_eq_cup {A B : Set α} : A ⊆ B ↔ A ∪ B = B := by
  apply Iff.intro
  case mp =>
    intro seq
    rw [eqr]
    intro x
    apply Iff.intro
    case mp =>
      intro xiaob
      apply (Or.elim xiaob) (seq x)
      intro b
      exact b
    case mpr =>
      intro xib
      exact Or.inr xib
  case mpr =>
    rw [eqr]
    intro xs x xia
    have h : x ∈ B := Iff.mp (xs x) (Or.inl xia)
    exact h

theorem not_cap_eq_cap {A B : Set α} : A \ (A ∩ B) = A \ B := sorry

-- example for relation syntax
theorem ex3 : (10000, 300000) ∈ { (x, y) | x < y } ∩ { (x, y) | x = 10000 } :=
  sorry
