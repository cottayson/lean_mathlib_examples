constant mynat : Type
-- https://leanprover.github.io/reference/declarations.html?highlight=assume
-- (Remember that ∀ is syntactic sugar for Π, and assume is syntactic sugar for λ.)
lemma func : nat → nat :=
begin
  intro n,
  exact 3*n+2,
end

#reduce func 5 -- 17
#reduce func 1 -- 5
#check func -- func : ℕ → ℕ
-- #eval func 7 -- code generation failed, VM does not have code for 'func'

-- level 3
lemma example2 (P Q R S T U: Type)
(p : P)
(h : P → Q)
(i : Q → R)
(j : Q → T)
(k : S → T)
(l : T → U)
: U :=
begin
  suffices q : Q,
    -- have q := h p,
    have t := j q, -- <=> have t : T, from j q,
    have u := l t,
    show U, from u,
  show Q, from h p, -- <=> exact h p,
end

#print example2
/-
λ (P Q R S T U : Type) 
(p : P) (h : P → Q) (i : Q → R) 
(j : Q → T) (k : S → T) (l : T → U), 
  l (j (h p))
-/

-- level 4
example (P Q R S T U: Type)
(p : P)
(h : P → Q)
(i : Q → R)
(j : Q → T)
(k : S → T)
(l : T → U)
: U :=
begin
  -- exact l (j (h p)),
  apply l,
 -- exact j (h p),
  apply j,
  -- exact h p,
  apply h,
  exact p,
end

-- level 5
example (P Q : Type) : P → (Q → P) :=
begin
  intro p, -- let p element in set P
  intro q, -- let q some element in set Q
  exact p, -- we already know that p is element in P, from hypothesis "p"
end

-- level 6
example (P Q R : Type) : (P → (Q → R)) → ((P → Q) → (P → R)) :=
begin
  intros f h p,
  apply f,
  -- first case P:
  exact p,
  -- second case Q:
  exact h p,
end
-- with refine
lemma example_refine (P Q R : Type) : (P → (Q → R)) → ((P → Q) → (P → R)) :=
begin
  intros f h p,
  -- refine f p _, exact h p, => goals accomplished
  -- refine f p (h p), -- => goals accomplished
  exact f p (h p),
end

#print example_refine
-- λ (P Q R : Type) (f : P → Q → R) (h : P → Q) (p : P), f p (h p)

-- with assume
lemma example_assume (P Q R : Type) : (P → (Q → R)) → ((P → Q) → (P → R)) :=
begin
  assume (f' : P → Q → R) (h' : P → Q) (p' : P),
  exact f' p' (h' p'),
end

#print example_assume
-- λ (P Q R : Type) (f' : P → Q → R) (h' : P → Q) (p' : P), f' p' (h' p')


-- level 8
example (P Q : Type) : (P → Q) → ((Q → empty) → (P → empty)) :=
begin
  intros f g h,
  -- apply g (f _),
  -- apply h,
  -- <=>
  exact g (f h),
end

-- level 9
example (A B C D E F G H I J K L : Type)
(f1 : A → B) (f2 : B → E) (f3 : E → D) (f4 : D → A) (f5 : E → F)
(f6 : F → C) (f7 : B → C) (f8 : F → G) (f9 : G → J) (f10 : I → J)
(f11 : J → I) (f12 : I → H) (f13 : E → H) (f14 : H → K) (f15 : I → L)
 : A → L :=
 begin
  intro a,
  apply f15, -- I
  -- apply f11, apply f10, -- I <=> same state as in previos row
  sorry,
 end

 -- Advanced proposition world.
--  Level 9: exfalso and proof by contradiction.
lemma contra (P Q : Prop) : (P ∧ ¬ P) → Q :=
begin
  sorry,
  have h : (P ∧ ¬ P) → false, 
  begin
    rw not_iff_imp_false,
    intro f,
    cases p with pt pf,
  end,
end

