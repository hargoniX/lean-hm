import Lean

def Set (α : Type u) := α → Prop

namespace Set

def mem (s : Set α) (a : α) := s a

notation:50 a " ∈ " s:50 => Set.mem s a

notation:55 a " ∉ " s:55 => ¬Set.mem s a

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

def subset (s₁ s₂ : Set α) : Prop :=
  s₁ ⊆ s₂ ∧ s₁ ≠ s₂

infix:75 " ⊂ " => Set.subset

def sdiff (s₁ s₂ : Set α) : Set α :=
  { a | a ∈ s₁ ∧ a ∉ s₂ }

infix:80 " \\ " => Set.sdiff

def empty : Set α := λ x => False

notation (priority := high) "∅" => empty

def univ : Set α := λ x => True

def compl (s₁ : Set α) : Set α := univ \ s₁

notation s "ᶜ" => compl s

theorem setext {A B : Set α} (h : ∀ x, x ∈ A ↔ x ∈ B) : A = B :=
  funext (λ x => propext (h x))

theorem inter_self_eq_self {A : Set α} : A ∩ A = A :=
  setext λ x => Iff.intro
    (λ ⟨h, _⟩ => h)
    (λ h => ⟨h, h⟩)

theorem inter_empty_eq_empty {A : Set α} : A ∩ ∅ = ∅ :=
  setext λ x => Iff.intro
    (λ ⟨_, h⟩ => h)
    (λ h => False.elim h)

theorem inter_comm {A B : Set α} (h : x ∈ A ∩ B) : x ∈ B ∩ A :=
  And.intro h.right h.left

theorem union_comm {A B : Set α} (h : x ∈ A ∪ B) : x ∈ B ∪ A := by
  apply Or.elim h
  case left =>
    intro xia
    exact Or.inr xia
  case right =>
    intro xib
    exact Or.inl xib

theorem subseteq_iff_inter_eq {A B : Set α} : A ⊆ B ↔ A ∩ B = A := by
  apply Iff.intro
  case mp =>
    intro seq
    apply setext
    intro x
    apply Iff.intro
    case mp =>
      intro xiab
      apply And.left xiab
    case mpr =>
      intro x₂
      have h : x ∈ B := (seq x) x₂
      exact And.intro x₂ h
  case mpr =>
    intro xs x xia
    rw [xs.symm] at xia
    exact And.right xia

theorem subseteq_iff_union_eq {A B : Set α} : A ⊆ B ↔ A ∪ B = B := by
  apply Iff.intro
  case mp =>
    intro seq
    apply setext
    intro x
    apply Iff.intro
    case mp =>
      intro xiaob
      apply (Or.elim xiaob) (seq x)
      exact id
    case mpr =>
      intro xib
      exact Or.inr xib
  case mpr =>
    intro xs x xia
    have h : x ∈ A ∪ B := Or.inl xia
    rw [xs] at h
    exact h

theorem sdiff_inter_eq_sdiff {A B : Set α} : A \ (A ∩ B) = A \ B := by
  apply setext
  intro x
  apply Iff.intro <;>
  {
    intro h;
    apply And.intro;
    case left =>
      exact h.left
    case right =>
      intro h₂
      apply h.right
      first | exact And.intro h.left h₂ | exact h₂.right
  }

end Set  
