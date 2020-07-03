set_option trace.simplify.rewrite true

open list(nil)

constant α : Type
constants reverse reverse2 : list α → list α
constant append : list α → α → list α

axiom append.base (x : α) : append nil x = [x]
axiom append.step (x y : α) (xs : list α) :
  append (x :: xs) y = x :: append xs y

axiom reverse.base : reverse nil = nil
axiom reverse.step (x : α) (xs : list α) :
  reverse (x :: xs) = append (reverse xs) x

attribute [simp] append.base append.step reverse.base reverse.step

example (x y z : α) : append [x, y] z = [x, y, z] :=
begin
  rw append.step,
  rw append.step,
  rw append.base,
end

lemma reverse.single (x : α) : reverse [x] = [x] :=
begin
  -- simp, give the same steps for proof
  rw reverse.step,
  rw reverse.base,
  rw append.base,
end

lemma reverse_twice.single (x : α) : reverse (reverse [x]) = [x] :=
begin
  rw reverse.step,
  rw reverse.base,
  rw append.base,
  rw reverse.step,
  rw reverse.base,
  rw append.base,
end

lemma reverse_twice.two (x y : α) : reverse (reverse [x, y]) = [x, y] :=
begin
  rw reverse.step,
  rw reverse.step,
  rw reverse.base,
  rw append.base,
  -- ⊢ reverse (append [y] x) = [x, y] ~
  -- reverse (append xs x) = x :: reverse xs
  rw append.step,
  rw reverse.step,
  rw append.base,
  rw reverse.step,
  rw reverse.base,
  rw append.base,
  rw append.step,
  rw append.base,
end

-- reverse (y :: xs) = append (reverse xs) y
example (x y : α) (xs : list α) :
  reverse (x :: y :: xs) = append (append (reverse xs) y) x :=
begin
  rw reverse.step,
  rw reverse.step,
  -- rw ←reverse.step,
  -- rw ←reverse.step,
end

lemma reverse_right (x : α) (xs : list α) :
  reverse (append xs x) = x :: reverse xs :=
begin
  induction xs with head tail ih,
  case nil {
    simp,
    -- rw append.base,
    -- rw reverse.step,
    -- rw reverse.base,
    -- rw append.base,
  },
  case cons {
    -- simp [ih],
    -- 1st way:
  -- [append.step]: append (head :: tail) x ==> head :: append tail x
  -- [reverse.step]: reverse (head :: append tail x) ==> append (reverse (append tail x)) head
  -- [ih]: reverse (append tail x) ==> x :: reverse tail
  -- [append.step]: append (x :: reverse tail) head ==> x :: append (reverse tail) head
  -- [reverse.step]: reverse (head :: tail) ==> append (reverse tail) head
    rw append.step,
    rw reverse.step,
    rw ih,
    rw append.step,
    rw reverse.step, -- rw ←reverse.step, also works because equality

    -- 2nd way:
    -- rw reverse.step,
    -- rw append.step,
    -- rw reverse.step,
    -- rw ←append.step,
    -- congr,
    -- exact ih,
  },
end

lemma reverse_twice.induction_step (x : α) (xs : list α) :
  reverse (reverse xs) = xs →  reverse (reverse (x :: xs)) = x :: xs :=
begin
  intros h,
  rw reverse.step,
  rw reverse_right,
  congr,
  exact h,
end

theorem reverse_twice (xs : list α) : reverse (reverse xs) = xs :=
begin
  induction xs with head tail ih,
  repeat { rw reverse.base, },
  simp [ih, reverse_right],
  -------------------------
  -- rw reverse.step,
  -- rw reverse_right,
  -- rw ih,
  -------------------------
  -- rw reverse.step,
  -- have h : ∃ (y : α) (ys : list α), y :: ys = tail, sorry,
  -- rw ←h,

  -- rw ←reverse.step at ih,
  -- rw reverse.step,
  -- have h : ∀ (l1 l2 : list α) (x : α), l1 = l2 → x :: l1 = x :: l2, sorry,
  -- have H := h (reverse (reverse tail)) tail head,
  -- have ih2 := H ih,
  -- apply eq.trans _ ih2,
  -- rw append.step,
end

#print reverse_twice
-- #eval cons 1 nil -- [1]

-- how to prove without lemma reverse_right:
theorem reverse_twice₂ (xs : list α) : reverse (reverse xs) = xs :=
begin
  induction xs with y ys ih,
  repeat { rw reverse.base },
  -- rw reverse.step,
  induction ys with z zs ih2, -- I think two induction steps need to prove without lemma reverse_right, because we have one in reverse_twice proof and have another in reverse_right proof.
  case nil {
    simp [reverse.base, append.base, reverse.step],
  }, 
  case cons {
    rw reverse.step,
    -- rw reverse_right,
    -- have rev_right := reverse_right y (reverse (z :: zs)),
    have rev_right : reverse (append (reverse (z :: zs)) y) =
                       y :: reverse (reverse (z :: zs)),
      {
        induction (reverse (z :: zs)) with head tail ih3,
        {
          rw append.base,
          rw reverse.base,
          exact reverse.single y,
        },
        {
          rw append.step,
          rw reverse.step,
          rw ih3,
          rw append.step,
          congr,
          rw reverse.step,
        },
      },
    rw rev_right,
    rw ih,
  },
end

example (β : Type) [decidable_eq β] (x : β) (xs : list β) :
  (x :: xs) ∩ xs = xs :=
begin
  change (list.inter (x :: xs) xs = xs),
  simp [list.inter],
  induction xs with head tail ih,
  simp,
  simp,
  sorry,
end

example (xs : list α) : list.append xs nil = xs :=
begin
  sorry,
end