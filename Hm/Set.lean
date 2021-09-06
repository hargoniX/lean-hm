import Lean

def Set (α : Type u) := α → Prop

namespace Set

def mem (s : Set α) (a : α) := s a

notation:50 a " ∈ " s:50 => Set.mem s a

notation:55 a " ∉ " s:55 => ¬Set.mem s a

def pred (p : α → Prop) : Set α := p

notation "{" a "|" p "}" => Set.pred (λ a => p)
-- TODO look into how we can implement notation like { a ∈ S | p a }

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

postfix:max "ᶜ" => compl

def powerset (s : Set α) : Set (Set α) := {t | t ⊆ s}

prefix:60 "𝒫" => powerset

-- This section provides usability lemmas so people don't have to
-- see the guts of the definition they are working with.
section usability

theorem mem_union (x : α) (A B : Set α) : x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B := Iff.rfl
theorem mem_union_of_left (x : α) (A B : Set α) : x ∈ A → x ∈ A ∪ B := Or.inl
theorem mem_union_of_right (x : α) (A B : Set α) : x ∈ B → x ∈ A ∪ B := Or.inr

theorem mem_inter (x : α) (A B : Set α) : x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B := Iff.rfl
theorem mem_inter_of_left_right (x : α) (A B : Set α) : x ∈ A → x ∈ B → x ∈ A ∩ B := And.intro

theorem subseteq_def (A B : Set α) : A ⊆ B ↔ (∀ x, x ∈ A → x ∈ B) := Iff.rfl

theorem subsete_def (A B : Set α) : A ⊂ B ↔ (A ⊆ B ∧ A ≠ B) := Iff.rfl

theorem mem_sdiff (x : α) (A B : Set α) : x ∈ A \ B ↔ x ∈ A ∧ x ∉ B := Iff.rfl

theorem not_mem_empty (x : α) : x ∉ ∅ := id

theorem mem_univ (x : α) : x ∈ univ := True.intro

theorem mem_compl (x : α) (A : Set α) : x ∈ Aᶜ ↔ x ∉ A :=
  Iff.intro (λ h1 h2 => h1.right h2) (λ h => ⟨True.intro, h⟩)

theorem mem_powerset (A B : Set α) : A ∈ (𝒫 B) ↔ A ⊆ B := Iff.rfl

end usability

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

theorem eq_empty_iff_all_notin {A : Set α} : (A = ∅) ↔ (∀ x, x ∉ A) := by
  apply Iff.intro
  case mp =>
    intro hA x xiA
    rw [hA] at xiA
    exact xiA
  case mpr =>
    intro hA
    apply setext
    intro x
    apply Iff.intro
    case h.mp =>
      intro xiA
      exact hA x xiA
    case h.mpr =>
      intro xiE
      exact False.elim $ xiE


theorem inter_comm {A B : Set α} : A ∩ B = B ∩ A :=
  setext λ x => Iff.intro
    (λ ⟨l, r⟩ => ⟨r, l⟩)
    (λ ⟨l, r⟩ => ⟨r, l⟩)

theorem union_comm {A B : Set α} : A ∪ B = B ∪ A := by
  apply setext
  intro x
  apply Iff.intro <;>
  {
    intro h;
    cases h with
    | inl h2 => exact Or.inr h2
    | inr h2 => exact Or.inl h2
  }

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

theorem any_subseteq_univ (A : Set α) : A ⊆ univ := λ _ _ => True.intro

def cartesian (s₁ : Set α) (s₂ : Set β) : Set (α × β) :=
  {t | t.fst ∈ s₁ ∧ t.snd ∈ s₂}
  
theorem any_subseteq_cartesian_univ_univ (A : Set (α × α)) :  A ⊆ cartesian Set.univ Set.univ := by
  intro _ _
  apply And.intro <;> exact True.intro

end Set  
