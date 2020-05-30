/-
Source: https://primes.utm.edu/notes/proofs/infinite/euclids.html
Theorem.
  There are more primes than found in any finite list of primes
Proof.
  Call the primes in our finite list p_1, p_2, ..., p_r.
    Let P be any common multiple of these primes plus one 
  (for example P = p_1 * p_2 * ... * p_r + 1).
  Now P is either prime or it is not. If it is prime,
  then P is a prime that was not in out list.
  If P is not prime, then it is divisible by some prime, call it p.
  Notice p can not be any of p_1, p_2, ..., p_r, otherwise
  p would divide 1, which is impossible. 
    So this prime p is some prime that was not in our original list.
  Either way, the original list was incomplete.
-/

import data.nat.prime

open nat

-- source: https://github.com/semorrison/lean-tidy/blob/master/examples/primes.lean
theorem exists_infinite_primes : ∀ n : ℕ, ∃ p, p ≥ n ∧ prime p :=
λ n,
  let p := min_fac (fact n + 1) in
  have fp : fact n > 0 := fact_pos n,
  have f1 : fact n + 1 ≠ 1, from ne_of_gt $ succ_lt_succ $ fact_pos n,
  have pp : prime p, from min_fac_prime f1,
  have w : n ≤ p, from le_of_not_ge $ λ h,
    have h₁ : p ∣ fact n, from dvd_fact (min_fac_pos (fact n + 1)) h,
    have h₂ : p ∣ 1, from (nat.dvd_add_iff_right h₁).2 (min_fac_dvd (fact n + 1)),
    pp.not_dvd_one h₂,
  ⟨p, w, pp⟩