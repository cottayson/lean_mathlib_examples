namespace hidden

inductive mynat
| zero : mynat
| succ : mynat → mynat

instance : has_zero mynat := ⟨mynat.zero⟩
instance : has_one mynat := ⟨mynat.succ mynat.zero⟩

def add : mynat → mynat → mynat
| n 0 := n
| n (mynat.succ m) := mynat.succ (add n m)

instance : has_add mynat := ⟨add⟩

@[pattern] def mul : mynat → mynat → mynat
| n 0 := 0
| n (mynat.succ m) := mul n m + n

instance : has_mul mynat := ⟨mul⟩

def pow : mynat → mynat → mynat
| n 0 := 1
| n (mynat.succ m) := pow n m * n

instance : has_pow mynat mynat := ⟨pow⟩
variables a b c : mynat

lemma pow_zero : a ^ (0 : mynat) = 1 := by { dsimp [(^)], rw pow }
lemma pow_succ : a ^ (mynat.succ b) = a ^ b * a := by { dsimp [(^)], rw pow }
example : 5 * (1 : mynat)  = 5 := rfl
lemma mul_one : a * (1 : mynat) = a := by {
  -- dsimp [(*)],
  -- unfold mul,
  -- refl,
  type_check mul,
  sorry,
}

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
  have step := λ x, pow_succ 1 x,
  apply mynat.rec_on m,
  exact base,
  intros a h₁,
  rw (step a),
  rw mul_one,
  exact h₁,
-- m : mynat,
-- base : 1 ^ 0 = 1,
-- step : 1 ^ succ m = 1 ^ m
-- ⊢ 1 ^ m = 1
  -- conv at step {
    -- congr,
    -- 2 goals
    -- m : mynat,
    -- base : 1 ^ 0 = 1,
    -- step : 1 ^ succ m = 1 ^ m
    -- | 1 ^ succ m
    
    -- m : mynat,
    -- base : 1 ^ 0 = 1,
    -- step : 1 ^ succ m = 1 ^ m
    -- | 1 ^ m
  -- },
end

end hidden