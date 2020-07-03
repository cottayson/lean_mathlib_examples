import tactic
-- 1.
-- #eval is_true (∀ x, x < 5 → ∃ y, y < x ∧ y*y = x)

-- 2.
namespace ex_2

constants (prime: ℕ → Prop) (coprime : ℕ → ℕ → Prop)
theorem prime.coprime_iff_not_dvd {p n : ℕ} (pp : prime p) : 
  coprime p n ↔ ¬ p ∣ n := sorry

theorem prime.dvd_iff_not_coprime {p n : ℕ} (pp : prime p) :
  p ∣ n ↔ ¬ coprime p n := sorry

theorem prime.dvd_mul {p m n : ℕ} (pp : prime p) :
  p ∣ n * m ↔ p ∣ m ∨ p ∣ n := sorry

end ex_2

-- source: https://github.com/enharsha/hello-world
namespace ex_3

variables (α : Type) (p q : α → Prop)

example: (∀x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
iff.intro
(assume h: (∀ x,p x ∧ q x), and.intro (assume h1 : α, (h h1).left) (assume h2 : α, (h h2).right))
(assume h: (∀ x, p x) ∧ (∀ x, q x), assume h1 : α, and.intro (h.left h1) (h.right h1))

example: (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
assume h1: (∀ x, p x → q x), assume h2: (∀ x, p x), assume h3: α, (h1 h3) (h2 h3)

example: (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
assume h: (∀ x, p x) ∨ (∀ x, q x), assume x : α,
or.elim h (assume h1 : ∀ x, p x, or.inl (h1 x)) (assume h2 : ∀ x, q x, or.inr (h2 x))

variables (men : Type) (barber : men)
variable (shaves : men → men → Prop)

--- false means contradiction
example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : false := 
have h1 : shaves barber barber ↔ ¬shaves barber barber, from (h barber),
have h2 : ¬ shaves barber barber, from (assume h3 : shaves barber barber, absurd h3 (h1.mp h3)),
false.elim (h2 (h1.mpr h2))

end ex_3

-- source: https://raw.githubusercontent.com/leanprover/lean2/227fcad22ab2bc27bb7471be7911075d101ba3f9/library/theories/number_theory/primes.lean
namespace ex_4

/-
definition infinite_primes (n : nat) : {p | p ≥ n ∧ prime p} :=
let m := fact (n + 1) in
have m ≥ 1,     from le_of_lt_succ (succ_lt_succ (fact_pos _)),
have m + 1 ≥ 2, from succ_le_succ this,
obtain p `prime p` `p ∣ m + 1`, from sub_prime_and_dvd this,
have p ≥ 2, from ge_two_of_prime `prime p`,
have p > 0, from lt_of_succ_lt (lt_of_succ_le `p ≥ 2`),
have p ≥ n, from by_contradiction
  (suppose ¬ p ≥ n,
    have p < n,     from lt_of_not_ge this,
    have p ≤ n + 1, from le_of_lt (lt.step this),
    have p ∣ m,     from dvd_fact `p > 0` this,
    have p ∣ 1,     from dvd_of_dvd_add_right (!add.comm ▸ `p ∣ m + 1`) this,
    have p ≤ 1,     from le_of_dvd zero_lt_one this,
    show false,     from absurd (le.trans `2 ≤ p` `p ≤ 1`) dec_trivial),
subtype.tag p (and.intro this `prime p`)

lemma exists_infinite_primes (n : nat) : ∃ p, p ≥ n ∧ prime p :=
exists_of_subtype (infinite_primes n)
-/
end ex_4

-- https://github.com/HoanNguyen92/example/tree/master/Lean
namespace ex_5

open nat int

#eval (-15 : ℤ) / 6 -- -3
#eval (-15 : ℤ) % 6 -- 3

lemma Lem1a (a : ℤ) : a ∣ 0 :=
begin
  simp[(∣)],
  existsi (0 : ℤ),
  rw mul_zero,
end

lemma Lem1b (a b : ℤ) : abs(b) < a ∧ b ≠ 0 → ¬ (b ∣ a) := sorry
theorem Thm1 (a b c : ℤ) : a ∣ b ∧ b ∣ c → a ∣ c := sorry
theorem Thm2 (a b c m n : ℤ) : c ∣ a ∧  c ∣ a → c ∣ (a*m + b*n) := sorry

def sumSeries {α : Type} (f : ℕ → α) [has_add α] : ℕ → α
| 0 := f 0
| (succ n) := (sumSeries n) + (f (n+1))

theorem Thm3 (f : ℕ → ℤ) (n : ℕ) (a : ℤ) :
  (∀ k : ℕ, k ≤ n → a ∣ f k) → 
  (∀ g : ℕ → ℤ, a ∣ sumSeries (λ x : ℕ, (f x) * (g x)) n) := sorry

#eval gcd (24:ℤ) 18 -- 6

#eval nat_abs (-1) -- 1

-- def zgcd (a b : ℤ) : ℤ := gcd (int.nat_abs a) (int.nat_abs b)
/- ambiguous overload, possible interpretations
  ↑(↑(a.nat_abs).gcd ↑(b.nat_abs))
  ↑(a.nat_abs.gcd b.nat_abs) -/

def zgcd (a b : ℤ) : ℕ := nat.gcd (int.nat_abs a) (int.nat_abs b)

#check gcd (-10:ℤ) (24) -- gcd works with ℤ type

lemma Lem2 (a b q r : ℤ) :
  a = b * q + r → gcd a b = gcd b r := sorry

-- def EuclideaAlgorithm : ℤ → ℤ → ℕ
-- | 0 b := nat_abs b
-- | a 0 := nat_abs a
-- | a b := EuclideaAlgorithm b (a % b)
-- failed to prove recursive application is decreasing

meta def EuclideaAlgorithm : ℤ → ℤ → ℕ
| 0 b := nat_abs b
| a 0 := nat_abs a
| a b := EuclideaAlgorithm b (a % b)

#eval EuclideaAlgorithm 24 18 -- 6
#eval EuclideaAlgorithm 4147 10672 -- 29
#eval gcd (4147:ℤ) 10672 -- 29

-- invalid definition, it uses untrusted declaration 'ex_5.EuclideaAlgorithm'
-- example : gcd (4147:ℤ) 10672 = EuclideaAlgorithm 4147 10672 := rfl

-- (n ≥ 2) ∧ (∀ m : ℕ, m ≥ 1 ∧ m ∣ n → (m = 1 ∨ m =n)) <=>
def isPrime (n : ℕ) : Prop :=
  n ≥ 2 ∧ ∀ (m : ℕ), m ≥ 1 ∧ m ∣ n → m = 1 ∨ m = n

#print isPrime -- let's look for the bracket structure

lemma helper : ∀ (a b : ℕ), a ≤ b + 1 → a = b + 1 ∨ a ≤ b :=
begin
  intros a b H,
  /-
    H : a ≤ b + 1
    ⊢ a = b + 1 ∨ a ≤ b
  if a ≤ b then a ≤ b + 1 using less_than_or_equal.step
  
  ¬ (a = b + 1 ∨ a ≤ b) ↔ ¬ (a = b + 1) ∧ ¬ (a ≤ b)
  a > b ∧ a ≠ b + 1 → a > b + 1 ↔ ¬ H
  (¬ goal → ¬ H) → (H → goal)
  apply (H → goal) H, Q.E.D
  -/
  sorry,
end

lemma two_is_prime : isPrime 2 :=
begin
  rw isPrime,
  split,
  change 2 ≤ 2, -- lean don't need this line
  exact less_than_or_equal.refl,
  intros m H,
  by_cases (m = 1),
  {
    left,
    exact h,
  },
  {
    have H2 := H.2,
    -- cases H2 with k,
    have lem1 : ∀ (a b : ℕ), a ∣ b → a ≤ b, {
      sorry,
    },
    type_check lem1 m 2,
    have m_le_2 := (lem1 m 2) H2,
    have H3 := helper m 1 m_le_2,
    change m = 2 ∨ m ≤ 1 at H3,
    sorry,
  },
end

lemma Lem3 (n : ℕ) :
  n > 1 → ∃ m : ℕ, isPrime m ∧ m ∣ n := sorry

theorem Thm4 (n : ℕ) :
  n > 1 ∧ ¬ isPrime n → ∃ m : ℕ, isPrime m ∧ m^2 ≤ n ∧ m ∣ n := sorry

def infinite (s : set ℕ) : Prop :=
  ∀ n : ℕ, ∃ m ∈ s, n < m

def TheSetOfPrimes := {n : ℕ | isPrime n}

theorem Thm5 : infinite TheSetOfPrimes :=
begin
  rw [TheSetOfPrimes, infinite],
  -- ⊢ ∀ (n : ℕ), ∃ (m : ℕ) (H : m ∈ {n : ℕ | isPrime n}), n < m
  sorry,
end

theorem DirichletThm (a b : ℤ) :
  a > 0 ∧ gcd a b = 1 → 
  infinite {n | isPrime n ∧ (∃ m : ℤ, ↑n = a * m + b)} := sorry

def modulo (a b : ℤ) (m : ℕ) : Prop :=
  ↑m ∣ a - b

local notation a `≡` b `mod` m  := modulo a b m

set_option trace.simplify.rewrite true

lemma LemCongruence (a b : ℤ) (m : ℕ) :
  (a ≡ b mod m) → ∃ k : ℤ, a = b + m * k :=
begin
  rw modulo,
  simp only [(∣)],
  intro H,
  cases H with t Ht,
  existsi t,
  rw ←Ht, -- rw (symm Ht),
  rw add_comm,
  rw sub_add_cancel,
  -- rw add_assoc,
  -- rw add_left_neg,
  -- rw add_zero,
end

def phi (n : ℕ) : ℕ → ℕ
| 0 := 0
| 1 := if n ≠ 0 then 1 else 0
| (m+2) := if nat.gcd ↑(m+2) n = 1 then phi (m+1) + 1 else phi (m+1)

def φ (n : ℕ) : ℕ := phi n (n-1)
#eval φ 8 -- 4
#eval φ 13 -- 12
#eval φ 1000 -- 400


end ex_5

-- https://github.com/hanzhi713/lean-proofs/blob/65d149e2185779c7444041f033d09b495cd86032/src/lessons/lesson8.lean
namespace ex_6

variables P Q : Prop

variable forward: P → Q
variable backward: Q → P

def pqEquiv : P ↔ Q := (iff.intro forward backward)
lemma pqEquiv' : P ↔ Q := (iff.intro forward backward)
#check pqEquiv -- ∀ (P Q : Prop), (P → Q) → (Q → P) → (P ↔ Q)
#check pqEquiv' -- ∀ (P Q : Prop), (P → Q) → (Q → P) → (P ↔ Q)
#check iff.elim_left (pqEquiv P Q forward backward) -- P → Q

end ex_6