-- lemma zero_pow_succ (m : mynat) : (0 : mynat) ^ (succ m) = 0 :=
-- begin
--   let h := pow_succ 0 _,
--   rw mul_zero at h,
--   exact h,
-- end

-- lemma pow_one (a : mynat) : a ^ (1 : mynat) = a :=
-- rw one_eq_succ_zero,
-- have h := pow_succ _ _, -- pow_succ a 0
-- rw h,
-- rw pow_zero,
-- exact one_mul _,

-- Level 4: one_pow
lemma one_pow (m : mynat) : (1 : mynat) ^ m = 1 :=
begin
  have base := pow_zero 1,
  have step := pow_succ 1 m,
  rw mul_one at step,
-- m : mynat,
-- base : 1 ^ 0 = 1,
-- step : 1 ^ succ m = 1 ^ m
-- ⊢ 1 ^ m = 1
  conv at step {
    congr,
    -- 2 goals
    -- m : mynat,
    -- base : 1 ^ 0 = 1,
    -- step : 1 ^ succ m = 1 ^ m
    -- | 1 ^ succ m
    
    -- m : mynat,
    -- base : 1 ^ 0 = 1,
    -- step : 1 ^ succ m = 1 ^ m
    -- | 1 ^ m
  }

end