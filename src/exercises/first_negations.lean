import data.int.parity
import data.real.basic
import .limit_definition -- <=> exercises.limit_definition

set_option trace.simplify.rewrite true

-- Negations, proof by contradiction and contraposition.
example : false → 0 = 1 :=
begin
  intro h,
  exfalso,
  exact h,
end

example {x : real} : ¬ x < x :=
begin
  intro hyp,
  rw lt_iff_le_and_ne at hyp,
  cases hyp with hyp_inf hyp_non,
  clear hyp_inf, -- we won't use that one, so let's discard it
  change x = x → false at hyp_non, -- Lean doesn't need this psychological line
  apply hyp_non (eq.refl x),
end

open int

example (n : ℤ) (h_pair : even n) (h_non_pair : ¬ even n) : 0 = 1 :=
begin
  have H : ¬ (0 = 1) := zero_ne_one,
  sorry,
end

example (P Q : Prop) (h₁ : P ∨ Q) (h₂ : ¬ (P ∧ Q)) : ¬ P ↔ Q :=
begin
  cases h₁,
  {
    have p_true : P = true, from sorry,
    rw p_true at h₂,
    have H : (true ∧ Q) = Q, from sorry,
    rw H at h₂,
    clear H,
    -- we must use maximum information rules:
    -- ¬ Q = (Q → false) give us less information than ¬ Q = (Q ↔ false)
    have H2 : ¬ Q ↔ (Q = false), from sorry,
    rw H2 at h₂,
    rename h₂ q_false,
    rw [p_true, q_false],
    -- simp only [iff],
    rw not_true,
    -- [not_true]: ¬true ==> false
    -- [iff_self]: false ↔ false ==> true
  },
  {
    sorry
  },
end

lemma ex1 (u : ℕ → ℝ) (l l' : ℝ) : seq_limit u l → seq_limit u l' → l = l' :=
begin
  intros hl hl',
  by_contradiction H,
  change l ≠ l' at H, -- for human readability
  have ineq : |l-l'| > 0,
    begin
    apply abs_pos_of_ne_zero, 
    -- backward proof: we need match goal to the right side of abs_pos_of_ne_zero:
    -- abs_pos_of_ne_zero : a ≠ 0 → |a| > 0
    --                              ↑↑↑↑↑↑↑
    -- then goal becomes left side: ⊢ l - l' ≠ 0
    apply sub_ne_zero_of_ne,
    exact H,
      -- exact abs_pos_of_ne_zero (sub_ne_zero_of_ne H),
    end,
  cases hl ( |l-l'|/4 ) (by linarith) with N hN, -- it's hard to understand this line
  cases hl' ( |l-l'|/4 ) (by linarith) with N' hN', -- and this
  let N₀ := max N N', -- this is a new tactic, whose effect should be clear
  specialize hN N₀ (le_max_left _ _),
  specialize hN' N₀ (le_max_right _ _),
  have clef : |l-l'| < |l-l'|,
    calc
    |l - l'| = |(l - u N₀) + (u N₀ - l')| : by ring
         ... ≤ |l - u N₀| + |u N₀ - l'|   : by apply abs_add -- apply in forward order, not backward?
         ... = |u N₀ - l| + |u N₀ - l'|   : by rw abs_sub
         ... < |l-l'| : by linarith,
  linarith, -- liarith can also find simple numerical contradictions
end

example (P Q : Prop) (h : ¬ Q → ¬ P) : P → Q :=
begin
  contrapose,
  exact h,
end
