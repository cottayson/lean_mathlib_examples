import tactic

namespace classes_example

universe u

class has_mul' (α : Type u) :=
  (mul : α → α → α)
  (mul_comm : ∀ (x y : α), mul x y = mul y x) -- (mul_comm (x y : α) : mul x y = mul y x)

def flip {α : Type u} := λ (f : α → α → α) {x y : α}, f y x

instance : has_mul' nat := {
  mul := λ m n, n * m, -- let's reverse order multiplication for fun!
  -- mul_comm := λ x y, nat.mul_comm y x
  mul_comm := λ x y, eq.symm $ nat.mul_comm x y
  -- mul_comm := flip nat.mul_comm -- NOT WORKS
}

class has_zero_one_and_mul (α : Type u) extends has_mul' α :=
(zero : α)
(one  : α)
(mul_zero : ∀ (x : α), mul x zero = zero)
(mul_one  : ∀ (x : α), mul x one = x)

@[instance] def instance1 : has_zero_one_and_mul nat := {
    zero := 0
  , one  := 1
  , mul_zero := λ x,
      begin
        unfold has_mul'.mul,
        apply eq.subst (nat.mul_comm 0 x),
        apply eq.refl,
      end
  , mul_one := begin apply nat.one_mul end
}

#print instance1

#print instance1._proof_1
-- not generated, but if we replace proof of mul_one with sorry then we see _proof_2
-- #print instance1._proof_2 

@[instance] def instance2 : has_zero_one_and_mul nat := /- ⟨0, 1, _, _⟩ -/ -- check this
  ⟨0, 1, nat.zero_mul, nat.one_mul⟩

end classes_example

namespace proofs_about_classes

open classes_example

-- #check has_zero_and_one
universe u
variables {α : Type u}

-- how to write theorem:
/-
example (β : Type) : [has_mul β] ∧ [has_zero_and_one β] → [has_zero_and_one_and_mul β] := _
-/

local notation `mul'` := has_mul'.mul

example (x : α) [has_mul' α] : mul' x x = mul' x x := rfl

example (x y : α) [has_zero_one_and_mul α] : mul' x y = mul' y x := by {
  tactic.unfreeze_local_instances,
  rename _inst_1 i,
  type_check i.zero, -- α
  apply i.mul_comm,
}

end proofs_about_classes