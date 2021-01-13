-- import .options

set_option trace.simplify.rewrite true

inductive palindrome {α : Type} : list α → Prop
| nil : palindrome []
| single (x : α) : palindrome [x]
| sandwich (x : α) (xs : list α) (hxs : palindrome xs) :
  palindrome ([x] ++ xs ++ [x])

open list
variable α : Type

lemma rev_core_nil {ys : list α} : reverse_core ys nil = reverse ys := by rw reverse

set_option pp.generalized_field_notation false

namespace example_for_rev_append_cons
def ys := [1,2,3,4]
constant y : ℕ
example : reverse (y :: ys) = reverse ys ++ [y] := rfl
-- GOAL: ⊢ reverse (x :: xs ++ ys) = reverse ys ++ reverse (x :: xs)
end example_for_rev_append_cons
-- we have positive example means this lemma is potentially provable, and we can safely use sorry keyword

lemma rev_append_cons (y : α) (ys : list α) : 
  reverse (y :: ys) = reverse ys ++ [y] :=
begin
  induction ys,
  case nil {
    simp only [reverse, reverse_core, nil_append],
    split; refl,
  },
  case cons : x ys ih {
    sorry,
  },
end


lemma reverse_append {xs ys : list α} :
  reverse (xs ++ ys) = reverse ys ++ reverse xs :=
begin
  induction xs,
  case nil {
    rw [nil_append, reverse]; simp,
    rw [reverse_core, append_nil],
  },
  case cons : x xs ih {
    rw cons_append,
    iterate 2 { rw rev_append_cons },
    rw [←append_assoc, ih],
  },
end

lemma reverse_palindrome (xs : list α)
    (hxs : palindrome xs) :
  palindrome (reverse xs) :=
begin
  induction hxs,
  case palindrome.nil { exact palindrome.nil },
  case palindrome.single { exact palindrome.single hxs },
  case palindrome.sandwich : x xs hxs ih {
    simp only [reverse, reverse_append],
    -- type_check palindrome.sandwich _ (reverse xs) ih, -- palindrome ([?m_1] ++ reverse xs ++ [?m_1])
    exact palindrome.sandwich x (reverse xs) ih,
  },
end