namespace hidden

set_option trace.simplify true

@[class] structure group (α : Type) : Type :=
(mul : α → α → α)
(one : α)
(inv : α → α)
(mul_assoc : ∀a b c, mul (mul a b) c = mul a (mul b c))
(one_mul : ∀a, mul one a = a)
(mul_left_inv : ∀a, mul (inv a) a = one)

-- potential instance of group class
inductive ℤ₂ : Type
| zero
| one

def ℤ₂.add : ℤ₂ → ℤ₂ → ℤ₂
| ℤ₂.zero a       := a
| a       ℤ₂.zero := a
| ℤ₂.one  ℤ₂.one  := ℤ₂.zero

-- def ℤ₂.neg (a : ℤ₂) := a

notation `z0` := ℤ₂.zero
notation `z1` := ℤ₂.one

-- #reduce ℤ₂.neg z0 -- z0
-- #reduce ℤ₂.neg z1 -- z1

#print add_group

-- proof of fact that ℤ₂ structure is group
@[instance] def ℤ₂.add_group : add_group ℤ₂ :=
{
  add := ℤ₂.add,
  add_assoc := begin sorry, end,
  zero := ℤ₂.zero,
  zero_add := begin sorry, end,
  add_zero := begin sorry, end,
  neg      := (λ x, x),
  add_left_neg := begin
    intro a,
    -- have h : Z₂.add_group.neg a = a,
    simp only [],
    cases a,
    trivial, -- or refl
    refl,
  end,
}

-- With this instance declaration, 
-- we can now use the notations 0, +, and -:
#reduce ℤ₂.one + 0 - 0 - ℤ₂.one -- ℤ₂.zero
#reduce ℤ₂.one + 0 + ℤ₂.one -- ℤ₂.zero

#reduce z0 + z0 -- z0
#reduce z0 + z1 -- z1
#reduce z1 + z0 -- z1
#reduce z1 + z1 -- z0
-- #reduce (3 : ℤ₂)

example (a : ℤ₂) : 
  a + a = z0 :=
begin
-- simp [ℤ₂.add], -- fails
  cases a; refl,  
end

lemma ex1 (a : ℤ₂) (b : ℤ₂) : 
  a ≠ b → a + b = z1 :=
begin
  intro h,
  cases a; cases b,
    exfalso, simp at h, exact h,
    refl,
    refl,
    exfalso, simp at h, exact h,
end

lemma ex2 (a : ℤ₂) (b : ℤ₂) : 
  a ≠ b → a + b = z1 :=
begin
  intro h,
  cases a; cases b,
  repeat {
    refl <|> { exfalso, simp at h, exact h },
  },
end
#print ex1
#print ex2

end hidden