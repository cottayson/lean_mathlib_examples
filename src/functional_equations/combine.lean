/-
| All possible ways to choose @k@ elements from a list, /with repetitions/. 
\"Symmetric power\" for lists. See also "Math.Combinat.Compositions".
From Math.Combinat.Sets

>>> combine 3 ['a','b','c']
["aaa","aab","aac","abb","abc","acc","bbb","bbc","bcc","ccc"]

>>> combine 4 ['a', 'b']
["aaaa","aaab","aabb","abbb","bbbb"]

combine :: Int -> [a] -> [[a]]
combine 0 _  = [[]]
combine k [] = []
combine k xxs@(x:xs) = map (x:) (combine (k-1) xxs) ++ combine k xs

| All possible ways to choose @k@ elements from a list, without
repetitions. \"Antisymmetric power\" for lists. Synonym for 'kSublists'.
*Perms> choose 2 [1,2,3,4]
[[1,2],[1,3],[1,4],[2,3],[2,4],[3,4]]

choose :: Int -> [a] -> [[a]]
choose 0 _  = [[]]
choose k [] = []
choose k (x:xs) = map (x:) (choose (k-1) xs) ++ choose k xs
-/

open list

#check @map -- (α → β) → list α → list β

constant  α : Type
constant combine : ℕ → list α → list (list α)
constant choose  : ℕ → list α → list (list α)

-- noncomputable instance : has_add α := ⟨list.append⟩

axiom combine.zero (xs : list α) : combine 0 xs = [[]]
axiom combine.empty (k : ℕ) : combine k [] = []
axiom combine.step (k : ℕ) (x : α) (xs : list α) :
  combine (k+1) (x::xs) = map (cons x) (combine k (x::xs)) ++ combine (k+1) xs

example : (λ (x : ℕ), x + 1) 5 = 6 := rfl
example : (λ (xs : list ℕ), 100 :: xs) [] = [100] := rfl

attribute [simp] combine.zero combine.empty

namespace helper
variable x : α
#reduce map (λ (ys : list α), x :: ys) [nil] ++ nil -- [[x]]
end helper

example : combine 0 [] = [[]] := combine.zero nil
example (x : α) : combine 1 [x] = [[x]] := by {
  rw [ combine.step, combine.zero, combine.empty ],
  refl,
}

set_option trace.simplify.rewrite true

namespace vars
variables (x y z : α) (xs ys zs : list α)

-- combine (k+1) (x:xs) = map (x:) (combine k (x:xs)) ++ combine (k+1) xs
-- combine 1 [x] = map (x:) (combine 0 [x]) ++ combine 1 [] = map (x:) [[]] ++ [] = [[x]]
example : combine 1 [x]       = [[x]]           := by simp [combine.step]
example : combine 1 [x, y]    = [[x], [y]]      := by simp [combine.step]
example : combine 1 [x, y, z] = [[x], [y], [z]] := by simp [combine.step]
example : combine 1 [x, y, z] = [[x], [y], [z]] := by iterate 3 { rw combine.step, simp }

example : combine 2 [x, y] = [[x, x], [x, y], [y, y]]                     := by simp [combine.step]
example : combine 2 [x, y, z] = [[x,x],[x,y],[x,z],[y,y],[y,z],[z,z]]     := by simp [combine.step]
example : combine 3 [x, y] = [[x, x, x], [x, x, y], [x, y, y], [y, y, y]] := by simp [combine.step]
end vars
-- [combine, choose] :: Int -> [a] -> [[a]]
-- [combine, choose] 0 _  = [[]]
-- [combine, choose] k [] = []

-- combine (k+1) (x:xs) = map (x:) (combine k (x:xs)) ++ combine (k+1) xs
-- choose  (k+1) (x:xs) = map (x:) (choose  k    xs ) ++ choose  (k+1) xs

-- axiom combine.step (k : ℕ) (x : α) (xs : list α) :
--   combine (k+1) (x::xs) = map (λ ys, x::ys) (combine k (x::xs)) ++ combine (k+1) xs

-- this two axioms may have contradiction ???
-- axiom choose.zero (xs : list α) : choose 0 xs = [[]]
-- axiom choose.empty (k : ℕ) : choose k [] = [] 

axiom choose.zero (xs : list α) : choose 0 xs = [[]]
axiom choose.empty (k : ℕ) : k ≥ 1 → choose k [] = []
axiom choose.step (k : ℕ) (x : α) (xs : list α) :
  choose (k+1) (x::xs) = map (cons x) (choose k xs) ++ choose (k+1) xs

attribute [simp] choose.zero choose.empty

example : choose 0 [] = [[]] := choose.zero nil
lemma one_nil   : choose 1 [] = [] := by rw [choose.empty]; repeat { apply nat.less_than_or_equal.refl <|> apply nat.less_than_or_equal.step }
lemma two_nil   : choose 2 [] = [] := by rw [choose.empty]; repeat { apply nat.less_than_or_equal.refl <|> apply nat.less_than_or_equal.step }
lemma three_nil : choose 3 [] = [] := by rw [choose.empty]; repeat { apply nat.less_than_or_equal.refl <|> apply nat.less_than_or_equal.step }

example (x : α) : choose 0 [x] = [[]] := choose.zero [x]
example (x : α) : choose 1 [x] = [[x]] := by {
  rw [ choose.step, choose.zero, choose.empty ],
  refl,
  exact nat.le_refl 1, -- <=> @nat.less_than_or_equal.refl 1
}
example (x : α) : choose 2 [x] = [] := by {
  simp [choose.step],
  iterate 2 { rw choose.empty },
  simp,
  iterate 3 { apply nat.less_than_or_equal.refl <|> apply nat.less_than_or_equal.step },
}

#check nat.less_than_or_equal.step

namespace vars2
variables (x y z w : α) (xs ys zs ws : list α)
-- choose (k+1) (x:xs) = map (x:) (choose k xs) ++ choose (k+1) xs
-- choose 1 [x] = map (x:) (choose 0 []) ++ choose 1 [] = map (x:) [] ++ [] = []

-- choose k (x:xs) = map (x:) (choose (k-1) xs) ++ choose k xs
-- choose 1 [x] = map (x:) (choose 0 []) ++ choose 1 [] = 
example : choose 1 [x] = [[x]] := by {
  simp [choose.step]; rw [choose.empty],
  apply nat.less_than_or_equal.refl <|> apply nat.less_than_or_equal.step,
}

example : choose 1 [x]       = [[x]]           := by simp [choose.step, one_nil]
example : choose 1 [x, y]    = [[x], [y]]      := by simp [choose.step, one_nil]
example : choose 1 [x, y, z] = [[x], [y], [z]] := by simp [choose.step, one_nil]
-- example : choose 1 [x, y, z] = [[x], [y]] := by iterate 3 { rw choose.step, simp }

-- induction forcing method:
-- 1. find symmetries, rules, shortest rules (requires minimum meta-rules that can generate rules), optimal path (list) of rules, "optimal path (method)" of calculating optimal paths(lists)...
-- 2. create set of hypothesis
-- 3. prove it or find a structure that simplifies task of proof in more general cases

-- group of steps for forcing cool_lemma1
example : choose 0 [] = [[]] := by simp [choose.step]
example : choose 1 [x] = [[x]] := by simp [choose.step, one_nil]
example : choose 2 [x, y] = [[x, y]] := by simp [choose.step, one_nil, two_nil]
example : choose 3 [x, y, z] = [[x, y, z]] := by simp [choose.step, one_nil, two_nil, three_nil]
lemma cool_lemma1 (n : ℕ): choose n xs = [xs] := sorry

example : choose 3 [x, y] = [] := by {
  repeat {
    simp [choose.step, one_nil],
    rw [choose.empty]; repeat { apply nat.less_than_or_equal.refl <|> apply nat.less_than_or_equal.step },
  },
}

example : choose 2 [x, y, z, w] = [[x,y],[x,z],[x,w],[y,z],[y,w],[z,w]] := by {
  repeat {
    simp [choose.step, one_nil],
    rw [choose.empty]; repeat { apply nat.less_than_or_equal.refl <|> apply nat.less_than_or_equal.step },
  },
}

example : choose 3 [x, y, z, w] = [[x,y,z],[x,y,w],[x,z,w],[y,z,w]] := by {
  repeat {
    simp [choose.step, one_nil],
    rw [choose.empty]; repeat { apply nat.less_than_or_equal.refl <|> apply nat.less_than_or_equal.step },
  },
}

end vars2