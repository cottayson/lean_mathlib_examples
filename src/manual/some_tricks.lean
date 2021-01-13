
import tactic.show_term
namespace beta_reduce

variables α : Type
variable m : α
set_option pp.beta true
#check (λ x (y : α → α), y x) m (λ n, n) -- m : α

end beta_reduce

axiom some : 1 = 1

#print axioms
#print notation ▸
#print prefix nat.add
#print classes -- add_comm_group, add_monoid, ...
#print instances add_monoid
#print fields add_monoid
#print fields add_group

/- -- version 1 --
add_group.zero         : α
add_group.neg          : α → α
add_group.add          : α → α → α

add_group.zero_add     : ∀ a : α,  0 + a = a
add_group.add_zero     : ∀ a : α,  a + 0 = a
add_group.add_left_neg : ∀ a : α, -a + a = 0

add_group.add_assoc    : ∀ a b c : α, (a + b) + c = a + (b + c)
-/

/- -- version 2 --
add_group.zero         : α
add_group.add_zero     : ∀ a : α,  a + 0 = a
add_group.zero_add     : ∀ a : α,  0 + a = a

add_group.neg          : α → α
add_group.add_left_neg : ∀ a : α, -a + a = 0

add_group.add          : α → α → α
add_group.add_assoc    : ∀ a b c : α, (a + b) + c = a + (b + c)
-/
example (p q : Prop) : p ∧ q → q ∧ p := by {
  intro h,
  cases h, -- like destruct in coq
  split,
  repeat { assumption },
}

example (p q : Prop) : p ∧ q → q ∧ p :=
assume hpq : p ∧ q,
have hp : p, from and.left ‹p ∧ q›,
have hq : q, from and.right ‹p ∧ q›,
show q ∧ p, from and.intro ‹q› ‹p›
-- ‹ = \f, › = \frq
-- ‹p› means (by assumption : p)
-- ‹_› means (by assumption : _) means (by assumption)



lemma test1 (a b : nat) : a + b = b + a := by show_term { ac_refl }
lemma test2 (a b c : nat) : a + (b + c) = (a + b) + c := by show_term { ac_refl }
#print test1 -- λ (a b : ℕ), ((is_commutative.comm b a).trans (eq.refl (a + b)).symm).symm
#print test2 -- λ (a b c : ℕ), ((is_associative.assoc a b c).trans (eq.refl (a + (b + c))).symm).symm

inductive nat' : Type
| zero' : nat'
| succ' : nat' → nat'

open nat'

def nat'_zero := zero'


@[instance] def nat'.has_zero : has_zero nat' := { zero := zero' }
@[instance] def nat'.has_one : has_one nat' := ⟨succ' zero'⟩
@[instance] def nat'.has_add : has_add nat' := {
  add := 
  (λ x y, 
    match x, y with
    | x, 0 := x
    | x, _ := 1
    end
  )
}

set_option pp.proofs true

lemma test_subst : 1 = 2 → 2 = 3 → 3 = 1 := λ h, eq.subst h eq.symm
lemma test_subst2 : 1 = 2 → 2 = 3 → 1 = 3 := λ h, h ▸ id
lemma test_trans : 1 = 2 → 2 = 3 → 1 = 3 := eq.trans --λ h₁ h₂, eq.trans h₁ h₂
lemma strange_proof (h₂ : 4 = 5 → 2 = 5) : 1 = 2 → 2 = 3 → 1 = 3 := λ h, h.symm ▸ h₂
lemma strange_proof2 (h₂ : 4 = 5 → 2 = 5) : 1 = 2 → 2 = 3 → 3 = 1 := λ h, h.symm ▸ (λ h₃, eq.symm (h₂ h₃))

#print test_subst

#check (0 + 1 : nat')

example : (0 : nat') = zero' := rfl

#check zero'


-- instance add_monoid : nat := {
--   add_monoid.zero
-- }

namespace red

constant g : nat → nat

noncomputable def f := g
example : f = g := rfl
-- attribute [irreducible] f
-- attribute [semireducible] f
attribute [reducible] f

example (a : nat) (H : a = g a) : f a = a :=
@@eq.subst 
  (λ x, f a = x)
  (eq.symm H)
  (eq.refl (f a))

end red

namespace smart_unfolding

constant n : nat
#reduce n + (nat.succ n) -- (n.add n).succ
set_option type_context.smart_unfolding false
#reduce n + (nat.succ n) 
-- ((nat.rec ⟨λ (a : ℕ), a, punit.star⟩
--     (λ (n : ℕ)
--      (ih : pprod (ℕ → ℕ) (nat.rec punit (λ (n : ℕ) (ih : Type), pprod (pprod (ℕ → ℕ) ih) punit) n)),
--        ⟨λ (a : ℕ), (ih.fst a).succ, ⟨ih, punit.star⟩⟩)
--     n).fst
--    n).succ

end smart_unfolding

namespace make_constructor_fresh_names
open tactic

inductive Foo
| mk₁ (a b c : nat) : Foo
| mk₂ (d e : bool) : Foo
| mk₃ (f g : Foo) : Foo


example (a b : nat) : a = a :=
by do
  ns ← mk_constructors_fresh_names `Foo,
  trace ns,
  constructor

end make_constructor_fresh_names