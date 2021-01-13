-- source: mathlib/test/simp_rw.lean
import tactic.simp_rw

set_option trace.simplify.rewrite true
-- `simp_rw` can perform rewrites under binders:
example : (λ (x y : ℕ), x + y) = (λ x y, y + x) := by simp [add_comm]
example : (λ (x y : ℕ), x + y) = (λ x y, y + x) := by simp_rw [add_comm]

-- `simp_rw` can apply reverse rules:
example (f : ℕ → ℕ) {a b c : ℕ} (ha : f b = a) (hc : f b = c) :
  a = c := by simp_rw [←ha, hc]

-- `simp_rw` performs rewrites in the given order
-- example {α β : Type} {f : α → β} {t : set β} :
--   (∀ s, f ∈ s ⊆ t) = ∀ s : set α, ∀ x ∈ s, x ∈ f t :=

-- `simp_rw` applies rewrite rules multiple times:
example (a b c d : ℕ) : a + (b + (c + d)) = ((d + c) + b) + a := by simp [add_comm]
example (a b c d : ℕ) : a + (b + (c + d)) = ((d + c) + b) + a := by simp_rw [add_comm]