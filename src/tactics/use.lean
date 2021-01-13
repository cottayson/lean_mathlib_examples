import tactic.push_neg
import data.int.basic

example (h : ∃ p: ℕ, ¬ ∀ n : ℕ, n > p) 
        (h' : ∃ p: ℕ, ¬ ∃ n : ℕ, n < p) :
        ¬ ∀ n : ℕ, n = 0 :=
begin
  push_neg at *,
  -- use 0,
  -- guard_target_strict 0 ≠ 0,
  use 42, -- 42 must be > 0 because <= we can prove (x : ℕ) ≠ 0 only for x > 0
end