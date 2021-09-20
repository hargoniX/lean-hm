import Hm.Set

class One (G : Type _) :=
  (one : G)

instance [s : One α] : OfNat α (nat_lit 1) where
  ofNat := s.one

class Inv (G : Type _) :=
  (inv : G → G)

postfix:max "⁻¹" => Inv.inv

class SemiGroup (G: Type _) extends Mul G :=
  mul_assoc : ∀ a b c : G, (a * b) * c = a * (b * c)

class Monoid (G: Type _) extends SemiGroup G, One G :=
  one_mul: ∀ a : G, 1 * a = a * 1
  mul_one: ∀ a : G, 1 * a = a * 1

class Group (G: Type _) extends Monoid G, Inv G :=
  mul_left_inv: ∀ a : G, a⁻¹ * a = 1

class AbelianGroup (G : Type _) extends Group G :=
  mul_comm : ∀ a b : G, a * b = b * a

structure SubGroup (G : Type _) [Group G] :=
  (carrier: Set G)
  (one_mem: 1 ∈ carrier)
  (mul_mem: ∀ a b, a ∈ carrier → b ∈ carrier → a * b ∈ carrier)
  (inv_mem: ∀ a, a ∈ carrier → a⁻¹ ∈ carrier)
