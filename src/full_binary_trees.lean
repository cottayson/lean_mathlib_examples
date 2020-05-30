/-5 .8 Summary of New Constructs
Lemmas:
  dec_trivial -- decidable truth (e.g., a true closed executable expression)
  funext      -- functional extensionality
  propext     -- propositional extensionality

Tactics:
  generalize -- replaces a term by a fresh variable defined by a new hypothesis
  linarith   -- applies a procedure for linear arithmetic
-/

namespace binary_trees

inductive btree (α : Type) : Type
| empty {} : btree
| node     : α → btree → btree → btree

def mirror {α : Type} : btree α → btree α
| btree.empty := btree.empty
| (btree.node (a : α) left right) := btree.node (a : α) (mirror right) (mirror left)

lemma mirror_mirror {α : Type} (t : btree α) :
  mirror (mirror t) = t :=
begin
  induction t with a l r ih_left ih_right,
  case btree.empty { refl },
  case btree.node {
    rw [mirror, mirror, ih_left, ih_right],
  },
end
#print mirror_mirror

lemma mirror_mirror₂ {α : Type} :
  ∀ t : btree α, mirror (mirror t) = t
| btree.empty := rfl
| (btree.node a l r) :=
  calc  mirror (mirror (btree.node a l r))
      = mirror (btree.node a (mirror r) (mirror l)) :
    by refl
  ... = btree.node a (mirror (mirror l)) (mirror (mirror r)) :
    by refl
  ... = btree.node a l (mirror (mirror r)) :
    by rewrite mirror_mirror₂ l
  ... = btree.node a l r :
    begin rewrite mirror_mirror₂ r, end -- another begin .. end syntax example
#print mirror_mirror₂

def singleton {α : Type} (a : α) : btree α :=
  btree.node a btree.empty btree.empty

#check btree.empty -- btree.empty : btree ?M_1
#check @btree.empty -- btree.empty : Π {α : Type}, btree α
#reduce @btree.empty nat -- btree.empty
#check btree.node 3 btree.empty btree.empty -- btree.node 3 btree.empty btree.empty : btree ℕ

example : singleton 3 = btree.node 3 btree.empty btree.empty := rfl

#reduce mirror (btree.node 10 (singleton 1) (singleton 2))
-- btree.node 10 (btree.node 2 btree.empty btree.empty) (btree.node 1 btree.empty btree.empty)

lemma mirror_singleton {α : Type} (a : α) :
  mirror (singleton a) = singleton a := rfl

example {α : Type} (a : α) (b : α) (c : α): 
  mirror (btree.node c (singleton a) (singleton b)) = (btree.node c (singleton b) (singleton a)) :=
begin
  -- simp [mirror],
  -- split; rw mirror_singleton, -- OK

  -- rw mirror,
  -- constructor, -- split also works

  refl,
end

/-
A binary tree is full if all its nodes have either zero or two children.
This can be encoded as an inductive predicate as follows:
-/

-- -- version 1
-- inductive is_full {α : Type} : btree α → Prop
-- | empty : is_full btree.empty -- maybe this <=> boolean True? => is_full btree.empty = true
-- | node (a : α) : 
--   (btree.node a (is_full btree.empty) (is_full btree.empty)) ∨ _

-- --version 2
-- inductive is_full {α : Type} : btree α → Prop
-- | empty : is_full btree.empty -- maybe this <=> boolean True? => is_full btree.empty = true
-- | node (a : α) : 
--   is_full (btree.node a (btree.empty) (btree.empty)) ∨
--   is_full (btree.node a (is_full (btree.node a _ _)) (is_full (btree.node a _ _)))

namespace test

inductive is_full {α : Type} : btree α → Prop
| empty : is_full btree.empty -- maybe this <=> boolean True? => is_full btree.empty = true
| node (a : α) : 
  is_full (btree.node a btree.empty btree.empty)

lemma is_full_singleton_test {α : Type} (a : α) :
  is_full (btree.node a btree.empty btree.empty) :=
begin
  -- rw is_full, -- fail
  -- rw is_full.node -- fail
  -- simp [is_full], -- fail

  -- constructor, -- OK
  -- cases is_full, -- fail
  -- by_cases is_full, --fail
  -- cases btree a, --fail
  -- cases is_full.node a, -- Doing nothing but no error
  -- refl, -- fail

  -- apply is_full.node, -- OK
  exact is_full.node a, -- OK
end

end test

-- version 4 -- invalid return type for 'binary_trees.is_full.node'
-- inductive is_full {α : Type} : btree α → Prop
-- | empty : is_full btree.empty
-- | node (a : α) {left : btree α} {right : btree α}
--   (hleft : is_full left) (hright : is_full right)
--   : 
--   (is_full (btree.node a btree.empty btree.empty)) ∨
--   (is_full (btree.node a left right))

-- NO ERROR
-- inductive is_full {α : Type} : btree α → Prop
-- | empty : is_full btree.empty
-- | node (a : α) {left right : btree α} : 
--   is_full (btree.node a left right)

namespace my_tries

inductive is_full {α : Type} : btree α → Prop
| empty : is_full btree.empty
| node (a : α) {left right : btree α} {l1 r1 l2 r2 : btree α}
  (hzero_or_two_children: 
    (left = btree.empty ∧ right = btree.empty) ∨
    (left = (btree.node a l1 r1) ∧ right = (btree.node a l2 r2))
  )
  : 
    is_full (btree.node a left right)

lemma is_full_singleton {α : Type} (a : α) :
  is_full (btree.node a btree.empty btree.empty) :=
begin
  constructor,
  simp,
  exact btree.empty,
  exact btree.empty,
  exact btree.empty,
  exact btree.empty,
end

/-
  A somethat more interesting property of full trees is that fullness
  is preserved by the mirror operation. Our first proof is by rule
  induction on ht : is_full t:
-/
lemma is_full_mirror {α : Type} (t : btree α)
    (ht : is_full t) :
  is_full (mirror t) :=
begin
  induction t with a left right ih_left ih_right,
  case empty {
    rw mirror,
    exact ht,
  },
  case node {
    rw mirror,
    sorry,
  },
end

end my_tries

namespace from_book

-- for example proposition always_true (btree α)
inductive always_true {α : Type} : btree α → Prop
| empty : always_true btree.empty
| node (a : α) : always_true (singleton a)

inductive is_empty {α : Type} : btree α → Prop
| empty : is_empty btree.empty

inductive is_not_empty {α : Type} : btree α → Prop
| node (a : α) : is_not_empty (singleton a)

inductive is_full {α : Type} : btree α → Prop
| empty : is_full btree.empty
| node (a : α) (left right : btree α)
    (h_full_left : is_full left) (h_full_right : is_full right)
    (hiff : left = btree.empty ↔ right = btree.empty) :
  is_full (btree.node a left right)

constants {α : Type} (a : α)

lemma is_full_singleton :
  is_full (singleton a) :=
begin
  apply is_full.node _ _ _,
  exact is_full.empty,
  exact is_full.empty,
  refl,
end
#print is_full_singleton
-- is_full.node a btree.empty btree.empty is_full.empty is_full.empty (iff.refl (btree.empty = btree.empty))

lemma is_full_singleton₂ : is_full (singleton a)  :=
    is_full.node -- function <=> rule <=> definition
      _ _ _ is_full.empty is_full.empty (iff.refl _) -- arguments <=> goals
-- first 3 solve automatically, but last 3 solve by human

lemma mirror_eq_empty_iff {α : Type} (l r : btree α): 
  (l = btree.empty ↔ r = btree.empty) →
  (mirror r = btree.empty ↔ mirror l = btree.empty) := sorry

-- proof by rule induction on ht : is_full t:
lemma is_full_mirror {α : Type} (t : btree α)
    (ht : is_full t) :
  is_full (mirror t) :=
begin
  induction ht,
  case is_full.empty {
    -- rw mirror,
    exact is_full.empty,
  },
  case is_full.node : a l r hl hr hiff ih_l ih_r {
    rewrite mirror,
    apply is_full.node,
    { exact ih_r },
    { exact ih_l },
    {
      simp [mirror_eq_empty_iff, *],
      sorry,
    },
  },
end

-- proof by structural induction on the tree t:
lemma is_full_mirror₂ {α : Type} :
  ∀ t : btree α, is_full t → is_full (mirror t)
| btree.empty := id
  -- begin
    -- assume ht : is_full btree.empty, <=> intro ht,
    -- exact ht,
    -- <=>
    -- exact id, -- <=> exact (λ ht, ht),
  -- end
| (btree.node a l r) :=
  begin
    intro ht,
    cases ht with _ _ _ hl hr hiff,
    rewrite mirror,

    -- α : Type,
    -- is_full_mirror₂ : ∀ (t : btree α), is_full t → is_full (mirror t),
    -- a : α,
    -- l r : btree α,
    -- hl hr : is_full l,
    -- hiff : l = btree.empty ↔ r = btree.empty
    -- ⊢ is_full (btree.node a (mirror r) (mirror l))
    apply is_full.node,
    {
      apply is_full_mirror₂, -- backward proof: goal changed from "is_full (mirror t)" to "is_full t"
      exact hr,
    },
    { exact is_full_mirror₂ _ hl }, -- same proof as in previous goal
    {
      -- simp [mirror_eq_empty_iff, *],
      sorry,
    },
  end


example : ¬ is_empty (singleton a) :=
begin
  assume h : is_empty (singleton a),
  cases (singleton a) with a left right,
  tactic.swap,
  -- rw is_empty.empty,
  sorry,
end

lemma empty_is_empty: is_empty (@btree.empty α) :=
begin
  -- refl, -- fail
  -- apply is_empty, -- fail
  exact is_empty.empty, -- OK
end


end from_book

-- When is_full function is undefined, proof of 1 = 1 using
-- is_full_singleton lemma works:
-- example : 1 = 1 :=
-- begin
--   have h := is_full_singleton btree.empty _,
--   refl,
--   exact nat,
-- end

end binary_trees