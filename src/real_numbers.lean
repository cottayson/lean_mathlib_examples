import data.real.basic

open tactic
set_option trace.simplify.rewrite true

constants a b c d : ℝ
example : (a * b) * c = b * (a * c) :=
begin
  -- simp only [mul_comm _ _, mul_assoc _ _ a], -- simp give infinite loop
  simp only [mul_comm _ b, mul_assoc _ _ _],
  -- rewrite mul_comm a b,
  -- rewrite mul_assoc b a c,
end

example (hyp : c = d*a + b) (hyp' : b = a*d) : c = 2*a*d :=
begin
  -- rw hyp' at hyp,
  -- rw hyp,
  -- rw mul_comm d _,
  -- rw ← two_mul _,
  -- rw ← mul_assoc 2 a d,
  -- simp [hyp'] at hyp,

  -- simp only [*, mul_comm, two_mul, mul_assoc] at *, -- fails
  -- 1 goal
  -- hyp' : b = a * d,
  -- hyp : c = a * d + a * d
  -- ⊢ a * d + a * d = d * (a + a)
  simp only [*, mul_comm, two_mul, mul_assoc, ← add_mul] at *, -- goals solved
-- [mul_comm]: d * a ==> a * d
-- [hyp']: b ==> a * d
-- [add_mul]: a * d + a * d ==> (a + a) * d
-- [mul_comm]: (a + a) * d ==> d * (a + a)
-- [[← add_mul]]: c ==> d * (a + a)
-- [two_mul]: 2 * a ==> a + a
-- [mul_comm]: (a + a) * d ==> d * (a + a)
end

example (hyp : c = b*a - d) (hyp' : d = a*b) : c = 0 :=
begin
  rw hyp' at hyp,
  rw hyp,
  simp only [sub_self, mul_comm],
end

example (hyp : c = d*a + b) (hyp' : b = a*d) : c = 2*a*d :=
begin
  calc c = d*a + b : by { rw hyp } -- ⊢ c = d * a + b
  ... = d*a + a*d  : by { rw hyp' } -- ⊢ c = 2 * a * b
  ... = a*d + a*d  : by { rw mul_comm d a } -- ⊢ d * a + a * d = a * d + a * d
  ... = 2*(a*d)    : by { simp [two_mul], } -- 
  ... = 2*a*d      : by { rw mul_assoc,},
end

example (hyp : c = d*a + b) (hyp' : b = a*d) : c = 2*a*d :=
begin
  calc c = d*a + b   : by rw hyp
     ... = d*a + a*d : by rw hyp'
     ... = 2*a*d     : by ring
end

example : a * (b * c) = b * (a * c) :=
begin
  ring,
end

lemma helper1 {x} : x < 1 → x = 0 := sorry

lemma l1 (x y) : x + y < 1 → x = 0 ∧ y = 0 :=
begin
  assume h₁,
  have h₆ : x + y = 0 := helper1 h₁,
  by_cases (x = 0),
  split, show_term { assumption, },
  rw h at h₁,
  show_term { simp at h₁,},
  
  -- show_term { solve_by_elim [helper1], },
  exact helper1 h₁,
  have h₂ : ¬x = 0 → x > 0 := sorry,
  have h₃ := h₂ h, clear h h₂,

  refine ⟨_, _⟩, -- ↔ split
  have h₄ : ∀ x, x < 0 → false := sorry,
  -- solve_by_elim [helper1] {discharger := cc},
  have h₇ : ∀ {n m} (k : ℕ), n > m → n + k > m + k := sorry,
  have h₈ := h₇ y h₃,
  
  -- show_term { finish [h₄, h₈], }, -- goal solved
  rw h₆ at h₈,
  show_term { solve_by_elim [h₄, h₈], }, -- OK
  -- exact false.elim (h₄ y h₈),
  
  -- apply h₄,
  /-
  x + y = 0, y = 0 → x = 0 
    (action: change goal to ⊢ y = 0)
  x + y = 0
  x > 0 => x = 1 ∨ x > 1
  ⊢ x = 0
  
  h₆ : ∀ (n m k), n > m → n + k > m + k
  x > 0 [h₆]=> x + y > y [x+y=0] => y < 0 => false

  n + m = k => n

  let x = 1 => false
  let x > 1 => x + y = 0
  -/
  sorry,
end

example : (a + b) * (a - b) = a^2 - b^2 := by ring