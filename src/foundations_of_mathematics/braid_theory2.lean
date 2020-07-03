import tactic.finish

namespace hidden

set_option trace.simplify.rewrite true
/-
bᵢ is Elementary braid, it is a crossing of two ropes i_th rope and (i+1)_th rope:
  bᵢ is counterclockwise crossing (if look from up (begining) to down (ending of braid))
  bᵢ⁻¹ is clockwise crossing

Properties of braid group:
G1. Associativity: ∀ a b c, a ∘ (b ∘ c) = (a ∘ b) ∘ c
G2. Identity: ∃! e, ∀ a, a ∘ e = e ∘ a = e
G3: Inverse: ∀ a, ∃! x, a ∘ x = x ∘ a = e
1. Trivial: bᵢ⁻¹ bᵢ = bᵢ bᵢ⁻¹ = e (it actually lemma from G3: Inverse)
2. Distant commutativity: if |i-j| ≥ 2 then bᵢ bⱼ = bⱼ bᵢ
3. Relation of Artin: bᵢ bᵢ₊₁ bᵢ = bᵢ₊₁ bᵢ bᵢ₊₁

Example:
b₃⁻¹ (b₂ b₃ b₂) b₃⁻¹ =
[by Artin relation]
(b₃⁻¹ b₃) b₂ (b₃ b₃⁻¹) =
[by Trivial]
e b₂ e =
[by id: λ x, e x = x]
b₂
-/



constant β : Type -- β is type of elementary rope crossing
constant B : ℕ → β -- Elementary braid (rope crossing)
constant e : β -- Identity braid

constant mul : β → β → β
constant inv : β → β

noncomputable instance : has_mul β := ⟨mul⟩
noncomputable instance : has_inv β := ⟨inv⟩

variables {a b c d : β}
variables {i j k : ℕ}

local notation `b0` := B 0
local notation `b1` := B 1
local notation `b2` := B 2
local notation `b3` := B 3
local notation `b4` := B 4
local notation `b5` := B 5
local notation `b6` := B 6
local notation `b7` := B 7
local notation `b8` := B 8
local notation `b9` := B 9

namespace braid

-- axiom b_zero : B 0 = e
-- Group axioms:
axiom assoc : a * b * c = a * (b * c)
-- axiom id.left : e * a = a
axiom id.right : a * e = a
axiom inv : a * a⁻¹ = e


-- Group lemmas:
lemma inv_left : a⁻¹ * a = e := by {
    rw ←@inv a,
    rw ←@id.right (a⁻¹ * a),
    rw ←@inv a⁻¹,
    rw ←@assoc (a⁻¹ * a) a⁻¹ a⁻¹⁻¹,
    -- simp only [assoc, id.right, inv],
    rw @assoc a⁻¹,
    rw @inv a,
    rw @id.right a⁻¹,
    rw @inv a⁻¹,
    -- exact @inv a⁻¹,
  }

lemma id.left : e * a = a := by rw [←@inv a, assoc, inv_left, id.right]

lemma mul_left  (h : a = b) (x : β) : x * a = x * b := sorry
lemma mul_right (h : a = b) (x : β) : a * x = b * x := sorry

lemma id_unique : a * b = a ↔ b = e := by {
    split; assume h,
      have H := mul_left h a⁻¹,
      rw ←assoc at H,
      rw inv_left at H,
      rw id.left at H,
      exact H,
    subst h,
    exact id.right,
  }
--
lemma inv_unique : a * b = e ↔ b = a⁻¹ := by {
    split; assume h,
      have H := mul_left h a⁻¹,
      rw [←assoc, inv_left, id.right, id.left] at H,
      exact H,
      -- have H := mul_right h b⁻¹,
      -- rw [assoc, inv, id.right, id.left] at H,
    rw [h, inv],
  }
--
lemma inv_inv : a⁻¹⁻¹ = a := by {
  conv { to_rhs, rw ←@id.right a },
  rw [←@inv a⁻¹, ←assoc, inv, id.left],
}
--
/-
  (a * b)⁻¹ = x
  e = (a * b) * x : from mul_left (a * b)
  e = a * (b * x) : from assoc
  a⁻¹ = b * x     : from mul_left a⁻¹
  b⁻¹ * a⁻¹ = x   : from mul_left b⁻¹
-/
lemma inv_two : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by {
  have h : a * b * b⁻¹ * a⁻¹ = e :=
    by rw [@assoc a b b⁻¹, inv, id.right, inv],
  calc (a * b)⁻¹ = (a * b)⁻¹ * e                    : (@id.right (a * b)⁻¹).symm
             ... = (a * b)⁻¹ * (a * b * b⁻¹ * a⁻¹)  : by rw h
             ... = (a * b)⁻¹ * (a * b) * b⁻¹ * a⁻¹  : by
               conv { to_rhs, rw [@assoc _ _ b⁻¹, @assoc _ _ a⁻¹] }
             ... = e * b⁻¹ * a⁻¹  : by rw inv_left
             ... = b⁻¹ * a⁻¹  : by { rw assoc, exact id.left },
  -- use this patern for building calc step by step:
  --         ... = _ : _
}

-- Braid axioms:
axiom dist_comm : i.succ < j → B i * B j = B j * B i
-- axiom dist_comm' (h : i.succ < j) : B i * B j = B j * B i
axiom artin : B i * B i.succ * B i = B i.succ * B i * B i.succ

open nat
-- Braid lemmas:
lemma triv : (B i) * (B i)⁻¹ = e := inv

lemma inv_left₂ : a⁻¹ * a = e := by {
    -- rw ←@inv a, -- ⊢ a⁻¹ * a = a * a⁻¹
    -- rw (@inv a).symm,
    -- type_check (@id _).1.symm,
    have m_left := λ x, (@id x).1.symm,
    have m_right := λ x, (@id x).2.symm,
    -- conv {
    --   trace_lhs,
    --   to_lhs,
    -- },
    -- rw m_left a⁻¹,
    -- rw ←@inv (a⁻¹ * a),
    rw (@inv a).symm,
    conv {
      to_lhs,
      rw m_left a⁻¹,
      rw ←@inv a,
    },
    conv {
      to_rhs,
      rw m_right a⁻¹,
    },
    -- how to ⊢ a * a⁻¹ * a⁻¹ * a = a * (a⁻¹ * e) -> ⊢ a * a⁻¹ * a⁻¹ * a = a * (a⁻¹ * a⁻¹) * a
  }

lemma inv_left₃ : a⁻¹ * a = e := by {
    have h := mul_right (@inv a) a,
    have h2 : e * a = a * e, from sorry,
    rw h2 at h,
    -- rw assoc at h,
    have h3 := (mul_left h a⁻¹),
    rw ←assoc at h3,
    rw ←@assoc a⁻¹ a e at h3,
  }

lemma inv_left₄ : a⁻¹ * a = e := by {
    have h1 := eq.refl a⁻¹,
    have h2 : a⁻¹ * e = a⁻¹, from sorry, clear h1,
    rw ←h2,
    rw ←@inv a,
    rw ←@assoc a⁻¹,
    rw @assoc (a⁻¹ * a),
  }

  lemma inv_left₅ : a⁻¹ * a = e := by {
    have h1 := eq.refl a⁻¹,
    have h2 : a⁻¹ * e = a⁻¹, from sorry, clear h1,
    have h3 : a⁻¹ * (a * a⁻¹) = a⁻¹, rw inv, exact h2,
    -- ⊢ a⁻¹ * a = e
    -- ⊢ a⁻¹ * a * a⁻¹ = e * a⁻¹
    -- ⊢ a⁻¹ * a * a⁻¹ = a⁻¹ by id.left
    -- ⊢ a⁻¹ * e = a⁻¹ by inv: a * a⁻¹ = e
    -- ⊢ a⁻¹ = a⁻¹ by id.right
  }


lemma dist_comm_inv :
  i.succ < j → (B i)⁻¹ * (B j)⁻¹ = (B j)⁻¹ * (B i)⁻¹ :=
  begin
    assume h_lt,
    have h_comm := @dist_comm i j h_lt,
    have h2 := mul_left h_comm (B i)⁻¹,
    rw ←assoc at h2,
    rw inv at h2,
  end

example : b0 * b2 = b2 * b0 := 
  begin
    -- simp [dist_comm, lt.base, lt.step], -- not works
    -- rw dist_comm, simp [dist_comm, lt.base], -- but this works
    -- simp [dist_comm, lt.base]; simp [dist_comm, lt.base, id, inv], -- not works
    repeat { rw dist_comm, simp [lt.base], }, -- ok
  end

example : e * e = e := id.left -- or id.right
example : a * (e * a) = a * a := by rw id.left
example : a * e * a = a * a := by rw id.right
example : a * e * a * e = a * a := by rw [id.right, id.right]

example : a * b * b⁻¹ * a⁻¹ = e := by rw [@assoc a b b⁻¹, inv, id.right, inv] -- proof with id.right
example : a * b * b⁻¹ * a⁻¹ = e := by simp [id.right, inv, assoc]
example : a * b * b⁻¹ * a⁻¹ = e := by rw [@assoc a b b⁻¹, inv, @assoc a e a⁻¹, id.left, inv] -- proof with id.left
example : a * b * b⁻¹ * a⁻¹ = e := by simp [id.left, inv, assoc]
example : b0 * b2 * b2⁻¹ * b0⁻¹ = e := by rw [@assoc b0 b2 b2⁻¹, triv, id.right, triv]

example : b2 * b0 = b0 * b2 := (λ h, (dist_comm h).symm) (lt.base 1)
example : b0 * b2 = b2 * b0 := dist_comm (lt.base 1)
example : b1 * b3 = b3 * b1 := dist_comm (lt.base 2)
example : b0 * b3 = b3 * b0 := dist_comm (lt.step (lt.base 1))
example (h : i ≥ 2) : (B 0 * B i) = (B i * B 0) := dist_comm h
example : i ≥ 2 → (B 0 * B i) = (B i * B 0) := λ h, dist_comm h

-- base state:
example : b0 * b1 * b0 = b1 * b0 * b1 := @artin 0
example : (b0 * b1) = (b1 * b0) * b1 * b0⁻¹ := by {
  -- 1. (b0 * b1) = (b1 * b0) * b1 * b0⁻¹
  -- 2. (b1 * b0⁻¹) = (b0⁻¹ * b1) * b0⁻¹ * b1⁻¹

  -- 1. (b0 * b1) = (b1 * b0) * (b0⁻¹ * b1) * b0⁻¹ * b1⁻¹ by subst 2.
  -- 1. (b0 * b1) = (b1 * b1) * b0⁻¹ * b1⁻¹               by id
  -- 1. (b0 * b1) = (b1 * b1) * (b1 * b1⁻¹) * b0⁻¹ * b1⁻¹ by id
  -- 1. (b0 * b1) = (b1 * b1) * b1 * b0⁻¹ * b1⁻¹ * b0⁻¹   by artin
    sorry,
  }
-- second state:
example : b1 * b0 * b1 = b0 * b1 * b0 := (@artin 0).symm
example : (b1 * b0) = (b0 * b1) * b0 * b1⁻¹ := by {
    sorry,
  }

/-
b0 b1 b2 b1
b0 b2 b1 b2 : from artin 1
b2 b0 b1 b2 : from dist_comm 0 2 (⊢ 1 < 2) =  dist_comm 0 2 (lt.base 1)
-/
example : b0 * b1 * b2 * b1 * b2⁻¹ * b1⁻¹ * b0⁻¹ = b2 := by
  rw [
    @assoc b0,
    @assoc b0,
    @artin 1, -- from artin 1
    ←@assoc b0,
    ←@assoc b0,
    @dist_comm 0 2 (lt.base 1), -- from dist_comm 0 2 (⊢ 1 < 2)
    @assoc (b2 * b0 * b1),
    triv,
    id.right,
    @assoc (b2 * b0),
    triv,
    id.right,
    @assoc b2,
    triv,
    id.right
  ]

example : b0 * b1 * b2 * b1 * b2⁻¹ * b1⁻¹ * b0⁻¹ = b2 := by {
    -- backtracking example
    -- rw @assoc b0, rw dist_comm, -- => ⊢ 1.succ < 2 => one of goals is not provable
    -- rw @assoc (b0 * b1), rw dist_comm, -- => ⊢ 1 < 1 => is not provable
    -- rw [@assoc b0, @assoc b0], rw dist_comm, -- => ⊢ 1 < 1 => is not provable
    -- simp [@assoc (b0), @assoc (b0), artin], rw dist_comm, -- ⊢ 1.succ.succ < 1 => not provable
    rw [@assoc (b0), @assoc (b0), artin, ← @assoc b0, ← @assoc b0],
    rw dist_comm, -- ⊢ 1 < 2 is provable! by lt.base 1
    any_goals { simp [lt.base, triv, id.right, assoc], },
  }


#check lt.trans (lt.base 0) (lt.base 1) = lt.step (lt.base 0) -- 0 < 1, 1 < 2 = 0 < 2 [by lt.trans]
example : 0 < 1 ∧ 1 < 2 → 0 < 2 := λ h, lt.trans h.left h.right
example : 0 < 1 → 0 < 2 := @lt.step 0 1
example : 0 < 2 := lt.trans (lt.base 0) (lt.base 1)
example : 0 < 2 := @lt.step 0 1 (lt.base 0)

example (a : Prop) : (a → true) ↔ true := iff.intro (λ _, trivial) (λ _ _, trivial)

end braid




end hidden


