import .reverse

set_option trace.simplify.rewrite true

#print reverse_right

open list(nil)

-- axiom append.base (x : α) : append nil x = [x]
-- axiom append.step (x y : α) (xs : list α) :
--   append (x :: xs) y = x :: append xs y

-- axiom reverse.base : reverse nil = nil
-- axiom reverse.step (x : α) (xs : list α) :
--   reverse (x :: xs) = append (reverse xs) x

axiom reverse2.base : reverse2 nil = nil -- nil ~ []
axiom reverse2.step (x y : α) (xs : list α) :
  reverse2 (append (x :: xs) y) = append (y :: reverse2 xs) x

attribute [simp] reverse2.base reverse2.step

-- how to prove that reverse2.single is not provable if we have only two axioms:
-- reverse2.base, reverse.step + append axioms
@[simp]
lemma reverse2.single (x : α) : reverse2 [x] = [x] :=
begin
  type_check append.base x,
  type_check append.step x x [],
  conv {
    to_lhs,
    rw ←append.base,
  },
  sorry,
end

lemma reverse2_right (x : α) (xs : list α) :
  reverse2 (append xs x) = x :: reverse2 xs :=
begin
  induction xs with y ys ih,
  { simp },
  -- rw append.step,
  rw reverse2.step,
  rw ←ih,
  sorry,
end

theorem reverse_and_reverse2_are_equivalent (xs : list α) :
  reverse xs = reverse2 xs :=
begin
  induction xs with y ys ih,
  {
    simp,
  },
  {
    simp [ih],
    induction ys with z zs ih2,
    { simp },
    
  },
end