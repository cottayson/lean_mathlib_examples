constant α : Type
constant reverse_core : list α → list α → list α
constant reverse : list α → list α
constant concat : list α → list α → list α

axiom reverse_core.base (l : list α) : reverse_core [] l = l
axiom reverse_core.step (x : α) (xs l : list α) :
  reverse_core (x :: xs) l = reverse_core xs (x :: l)

axiom reverse.def (xs : list α) : reverse xs = reverse_core xs []

axiom concat.base (l : list α) : concat [] l = l
axiom concat.step (x : α) (xs l : list α) :
  concat (x :: xs) l = x :: concat xs l

lemma reverse.single (x : α) : reverse [x] = [x] :=
begin
  rw reverse.def,
  rw reverse_core.step,
  rw reverse_core.base,
end

example (a b c : α) : reverse [a, b, c] = [c, b, a] :=
begin
  rw reverse.def,
  repeat { rw reverse_core.step },
  rw reverse_core.base,
end

-- local notation a `+++` b := concat a b

lemma concat.list_nil (l : list α) : concat l [] = l := sorry

lemma reverse_concat'' (xs ys : list α) :
  reverse (concat xs ys) = concat (reverse ys) (reverse xs) :=
begin
  repeat { rw reverse.def }, 
  induction xs with x xs ih, {
    rw reverse_core.base,
    rw concat.base,
    rw concat.list_nil,
  }, {
    rw reverse_core.step,
    rw concat.step,
    rw reverse_core.step,
    sorry,
  },
end

-- lemma reverse_concat' (xs ys : list α) :
--   reverse (concat xs ys) = concat (reverse ys) (reverse xs)
-- | []        ys :=
-- begin
  
-- end
-- | (x :: xs) ys := begin
  
-- end

-- lemma reverse_concat {α : Type} : ∀ xs ys : list α,
--   reverse (xs ++ ys) = reverse ys ++ reverse xs
-- | []        ys := by simp [reverse]
-- | (x :: xs) ys := by simp [reverse, reverse_append xs]