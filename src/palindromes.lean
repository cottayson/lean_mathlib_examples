import data.list
-- import .options

set_option trace.simplify.rewrite true

inductive palindrome {α : Type} : list α → Prop
| nil : palindrome []
| single (x : α) : palindrome [x]
| sandwich (x : α) (xs : list α) (hxs : palindrome xs) :
  palindrome ([x] ++ xs ++ [x])

open list

lemma reverse_palindrome {α : Type} (xs : list α)
    (hxs : palindrome xs) :
  palindrome (reverse xs) :=
begin
  induction hxs,
  case palindrome.nil {
    exact palindrome.nil,
  },
  case palindrome.single {
    exact palindrome.single hxs,
  },
  case palindrome.sandwich : x xs hxs ih {
    simp only [reverse, reverse_append],
    apply palindrome.sandwich _ _ _,
    exact ih,
  },
end