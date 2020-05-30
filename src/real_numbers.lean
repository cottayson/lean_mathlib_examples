import data.real.basic

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

example : (a + b) * (a - b) = a^2 - b^2 :=
begin
  simp,
end