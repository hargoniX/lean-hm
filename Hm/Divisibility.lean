def divides (a : Nat) (b : Nat) := ∃ k, a * k = b

infix:40 " | " => divides

theorem divides_def : a | b ↔  ∃ k, a * k = b := Iff.rfl
theorem divides_intro (k: Nat) : a * k = b → a | b := by
  intro h
  apply Exists.intro k
  exact h

theorem all_divide_zero : ∀ n, n | 0 := by
  intro n
  apply divides_intro 0
  simp

theorem divides_refl : ∀ n, n | n := by
  intro n
  apply divides_intro 1
  simp

theorem one_divides_all : ∀ n, 1 | n := by
  intro n
  apply divides_intro n
  simp

def common_divisor (g : Nat) (a: Nat) (b: Nat) := g | a ∧ g | b
def gcd_of (g : Nat) (a: Nat) (b: Nat) := (common_divisor g a b) ∧ ∀ t, common_divisor t a b → t | g
def coprime (a : Nat) (b : Nat) := gcd_of 1 a b
def prime (p : Nat) := 2 ≤ p ∧ ∀ n, n | p → (n = 1 ∨ n = p)

def common_divisor_def : common_divisor g a b ↔ g | a ∧ g | b := Iff.rfl
def common_divisor_intro : g | a → g | b → common_divisor g a b := And.intro
def gcd_of_def : gcd_of g a b ↔ (common_divisor g a b) ∧ ∀ t, common_divisor t a b → t | g := Iff.rfl
def gcd_of_intro : (common_divisor g a b) → (∀ t, common_divisor t a b → t | g) → gcd_of g a b := And.intro
def coprime_def : coprime a b ↔ gcd_of 1 a b := Iff.rfl
def prime_def : prime p ↔ 2 ≤ p ∧ ∀ n, n | p → (n = 1 ∨ n = p) := Iff.rfl
def prime_intro : 2 ≤ p → (∀ n, n | p → (n = 1 ∨ n = p)) → prime p := And.intro

-- TODO: lcm
-- TODO: constructive definition of gcd, lcm would be better
-- TODO: Theorems from the script

