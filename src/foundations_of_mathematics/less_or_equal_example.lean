namespace hidden

constant le : ℕ → ℕ → Prop
axiom le.refl {x : ℕ} : le x x
axiom le.step {x y : ℕ} : le x y → le x (y + 1)

attribute [simp] le.refl le.step
attribute [refl] le.refl

-- Examples:
  -- Implicit arguments:
  example : le 3 3 := le.refl
  example : le 2 3 := le.step le.refl
  -- example : le 2 3 := le.step (⊢ le 2 2)
  example : le 1 3 := le.step (le.step le.refl)
  -- example : le 1 3 := le.step (⊢ le 1 2)
  -- example : le 1 3 := le.step (le.step (⊢ le 1 1))

  -- Explicit arguments:
  example : le 3 3 := @le.refl 3
  example : le 2 3 := @le.step _ _ le.refl
  example : le 1 3 := @le.step _ _ (@le.step _ _ le.refl)

lemma zero_less_nat (n : ℕ) : le 0 n :=
begin
  induction n with n ih,
  case nat.zero { exact le.refl }, -- ⊢ le 0 0
  case nat.succ { -- ih : le 0 n
    exact le.step ih, -- ⊢ le 0 n.succ
  },
end

#print zero_less_nat
-- λ (n : ℕ), 
-- nat.rec le.refl (λ (n : ℕ) (ih : le 0 n), ih.step) n

lemma zero_less_nat₂ (n : ℕ) : le 0 n :=
begin
  apply nat.rec,
  -- and we have 2 goals:
  -- first: ⊢ le 0 0
  { exact le.refl },
  -- second: ⊢ ∀ (n : ℕ), le 0 n → le 0 n.succ
  { exact @le.step 0 },
end

#print nat.rec
#print nat.rec_on

lemma zero_less_nat₃ (n : ℕ) : le 0 n := 
  nat.rec le.refl (@le.step 0) n
  -- nat.rec le.refl (assume m, sorry) n
  -- nat.rec (⊢ le 0 0) (⊢ ∀ (n : ℕ), le 0 n → le 0 n.succ) n

#print zero_less_nat₃ -- λ (n : ℕ), nat.rec le.refl le.step n

lemma zero_less_nat₄ (n : ℕ) : le 0 n := 
  nat.rec le.refl (λ (m : ℕ), @le.step 0 m) n

#print zero_less_nat₄ -- λ (n : ℕ), nat.rec le.refl (λ (m : ℕ), le.step) n


-- try #1
example (n : ℕ) : n ≠ 0 → le 1 n :=
begin
  assume ne_zero : n ≠ 0, -- we in state A
  rw (ne.def n 0) at ne_zero,
  by_cases n = 0,
  apply absurd h ne_zero, -- the same state as state A
  sorry,
end

lemma le.branch {a b : ℕ} : le a b → a = b ∨ le a.succ b :=
begin
  assume le_a_b : le a b,
  by_cases (a = b),
  { left, exact h },
  {
    right,
    sorry,
  },

end

lemma ex1 (n : ℕ) : n ≠ 0 → le 1 n :=
begin
  intro ne_zero,
  have h : le 0 n := zero_less_nat n,
  type_check @le.branch 0 n, -- le 0 n → 0 = n ∨ le (0 + 1) n
  type_check le.branch h, -- 0 = n ∨ le (0 + 1) n
  have h_cases := le.branch h,

  cases h_cases with n_eq_zero n_ge_one, {
    type_check ((ne.def n) 0).mpr, -- we have two options: .mp and .mpr
    type_check ((ne.def n) 0).mp, -- but we need only .mp
    have ne_zero' := ((ne.def n) 0).mp ne_zero,
    exact absurd n_eq_zero.symm ne_zero',
  }, {
    exact n_ge_one,
  },
end

#print ex1
-- λ (n : ℕ) (ne_zero : n ≠ 0),
--   (zero_less_nat n).branch.dcases_on (λ (n_eq_zero : 0 = n), absurd n_eq_zero.symm ((ne.def n 0).mp ne_zero))
--     (λ (n_ge_one : le 1 n), n_ge_one)

lemma ex1₂ (n : ℕ) : n ≠ 0 → le 1 n :=
begin
  intro ne_zero,
  have h_cases := le.branch (zero_less_nat n),
  have ne_zero' := ((ne.def n) 0).mp ne_zero,
  type_check h_cases, -- 0 = n ∨ le 1 n
  apply (
    or.elim
      h_cases
      (λ (zero_eq_n : 0 = n), absurd zero_eq_n.symm ne_zero') -- λ zero_eq_n, ... also works
      (λ (x : le 1 n), x) -- ~ identity function (λ x, x) = id
  ),
end

lemma ex1₃ (n : ℕ) : n ≠ 0 → le 1 n :=
begin
  intro ne_zero,
  have h_cases : 0 = n ∨ le 1 n := le.branch (zero_less_nat n),
  have ne_zero' := ((ne.def n) 0).mp ne_zero,
  apply (
    or.elim
      h_cases
      (λ h₁, absurd _ ne_zero')
      (λ h₂, _) -- (λ h₂, h₂) ~ id
  ),
  exact h₁.symm, -- first goal
  exact h₂, -- second goal
end

lemma ex1₄ (n : ℕ) : n ≠ 0 → le 1 n :=
begin
  intro ne_zero,
  have h_cases : 0 = n ∨ le 1 n := le.branch (zero_less_nat n),
  have ne_zero' := ((ne.def n) 0).mp ne_zero,
  apply or.elim,
  apply h_cases,
  -- apply (λ h₁, absurd (eq.symm h₁) _),
  -- exact ne_zero',
  apply (λ h₁, absurd _ ne_zero), -- ne_zero ~ ne_zero'
  exact h₁.symm,
  exact id,
end

#print ex1₂
#print ex1₃
#print ex1₄ -- short proof
-- λ (n : ℕ) (ne_zero : n ≠ 0),
--   (zero_less_nat n).branch.elim
--     (λ (h₁ : 0 = n), absurd h₁.symm ne_zero)
--     id

-- Structured proof #1
lemma ex1₅ (n : ℕ) : n ≠ 0 → le 1 n :=
  assume ne_zero : n ≠ 0,
  have h_cases : 0 = n ∨ le 1 n, from le.branch (zero_less_nat n),
  h_cases.elim
    (λ h₁, absurd h₁.symm ne_zero)
    id

-- Structured proof #2
lemma ex1₆ (n : ℕ) : n ≠ 0 → le 1 n :=
  λ ne_zero : n ≠ 0, (zero_less_nat n).branch.elim
    (λ h₁ : 0 = n, absurd h₁.symm ne_zero)
    (λ h₂ : le 1 n, h₂)


example (n : ℕ) : n ≠ 0 ∧ n ≠ 1 → le 2 n := sorry
example (n : ℕ) : ¬(le n 1) → le 2 n := sorry
example (n m : ℕ) : ¬(le n m) → le m.succ n := sorry

example (n : ℕ) : le n (n+1) := le.step le.refl
example (n m : ℕ) : le n (n+m) := sorry

example (n : ℕ) : le n (2*n) :=
begin
  induction n with n ih,
  case nat.zero { exact le.refl },
  have h₂ := le.step (le.step ih),
  change le n (2 * n.succ) at h₂,
  have h₃ : n = 2 * n ∨ le n.succ (2 * n) := le.branch ih,
  cases h₃ with n_eq_two_n le_nsucc_two_n,
  {
    -- 1st way:
    -- have helper : ∀ m : ℕ, m ≠ 0 → n = m * n → n = 0, from sorry,
    -- rw (helper 2) _ n_eq_two_n,
    -- -- rw nat.mul,
    -- exact le.step le.refl,
    -- have two_ne_zero : 2 ≠ 0, from dec_trivial,
    -- exact two_ne_zero,

    -- 2nd way:
    -- have helper : ∀ m : ℕ, le 1 m → n = m * n → n = 0, from sorry,
    -- have n_zero: n = 0 := (helper 2) (le.step le.refl) n_eq_2n,
    -- rw n_zero,
    -- exact le.step le.refl,

    -- 3rd way:
    rw ←nat.add_one,
    change le _ (2 * n + 2),
    rw ←n_eq_two_n,
    exact le.step le.refl,
  },
  {
    exact le.step (le.step le_nsucc_two_n),
  },
end

example (n : ℕ) : le (2*n) (3*n) := sorry

example (n a b : ℕ) : le a b → le (a*n) (b*n) := sorry
example (a b n m : ℕ) : le a b → le m n → le (a*m) (b*n) := sorry

lemma not_le_succ_le_succ {m n : ℕ}: le (n + 1) m → le (m + 1) n → false :=
begin
  assume h₁ h₂,
  have helper : ∀ a b, ¬(le a b) ↔ le a.succ b, from sorry,
  have p1: Prop, sorry,
  have p2: Prop, sorry,
  have k : p1 = p2, sorry,
  type_check (eq.mp k),
  have h₃ : ¬le n m := (helper n m).mpr h₁,


end

-- which lemma are simplest for proving without other?
lemma not_le_succ_le_succ' {m n : ℕ}: ¬(le (n + 1) m ∧ le (m + 1) n) :=
  λ ⟨h₁, h₂⟩, (@not_le_succ_le_succ m n) h₁ h₂

example (n m : ℕ) : n = m ↔ le n m ∧ le m n :=
begin
  apply iff.intro, {
    assume n_eq_m : n = m,
    rw n_eq_m,
    rw and_self,
  }, {
    assume h_and : le n m ∧ le m n,
    -- by_cases (n = m), ~ by_contradiction
    -- { exact h },
    -- exfalso,
    by_contradiction n_neq_m,
    have h₁ := le.branch h_and.1,
    have h₂ := le.branch h_and.2,
    clear h_and,
    cases h₁; cases h₂; try { contradiction },
    exact absurd h₂.symm n_neq_m,
    change le (n+1) _ at h₁,
    change le (m+1) _ at h₂,
    -- apply (@not_le_succ_le_succ m n) h₁ h₂,
    exact (@not_le_succ_le_succ' m n) ⟨h₁, h₂⟩,
  },
end

end hidden

