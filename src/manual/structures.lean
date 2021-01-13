structure point := (x y : nat)

#check point.mk 1 2

lemma point_destruct (p₁ p₂ : point) : p₁ = p₂ → p₁.x = p₂.x ∧ p₁.y = p₂.y := by {
  intro h,
  -- split; congr; exact h,
  split; { 
    apply congr_arg,
    exact h,
  },
}

#check point.x
#check point.y

#check @congr_arg

lemma point_destruct' (p₁ p₂ : point) :
  p₁ = p₂ → p₁.x = p₂.x ∧ p₁.y = p₂.y := λ h, ⟨congr_arg point.x h, congr_arg point.y h⟩

#print point_destruct -- <=> point_destruct'

def point_arg {f : point → ℕ} {p₁ p₂ : point} : 
  p₁ = p₂ → f p₁ = f p₂ := λ h, @congr_arg _ _ p₁ p₂ f h

#check @congr_arg -- ∀ {α : Sort u_1} {β : Sort u_2} {a₁ a₂ : α} (f : α → β), a₁ = a₂ → f a₁ = f a₂
#check @point_arg --                      ∀ {f : point → ℕ} {p₁ p₂ : point}, p₁ = p₂ → f p₁ = f p₂

#check point_arg _

lemma point_destruct'' (p₁ p₂ : point) (h : p₁ = p₂) :
  p₁.x = p₂.x ∧ p₁.y = p₂.y := and.intro (point_arg h) (point_arg h)
-- branches: 1. (point_arg h) 2. (point_arg h) are equal each other.
-- Can we use this fact to simplify proof?
-- answers:
-- 0. Using notation keyword
-- 1. Using lemma keyword
-- 2. Using repeat tactic
-- 3. Using way like that: def helper {p : Prop} (hp : p) : p ∧ p := and.intro hp hp
#check @point_arg
#check @point.x

-- p.x <=> point.x p
lemma lemma1 (p q : point) (h : p = q) : point.y p = point.y q := point_arg h
lemma lemma2 {p q : point} {f : point → ℕ} (h : p = q) : f p = f q := point_arg h
-- maybe we should add one more argument to lemma2 => lemma2 !== point_arg

lemma point_destruct''_1 (p₁ p₂ : point) (h : p₁ = p₂) :
  p₁.x = p₂.x ∧ p₁.y = p₂.y := by { 
    apply and.intro,
    apply lemma2 h, -- lemma2 <=> point_arg, nothing new => wrong branch
    apply lemma2 h,
  }

-- Using repeat or iterate tactic: 
lemma point_destruct''_2 (p₁ p₂ : point) (h : p₁ = p₂) :
  p₁.x = p₂.x ∧ p₁.y = p₂.y := by { apply and.intro, iterate 2 { exact point_arg h }, }

def helper {p : Prop} (hp : p) : p ∧ p := and.intro hp hp

#print helper

-- helper h has type
--   p₁ = p₂ ∧ p₁ = p₂
-- but is expected to have type
--   p₁.x = p₂.x ∧ p₁.y = p₂.y

-- def helper2 (f g : point → ℕ) (rel : point → point → Prop) := refl.

constant rel : point → point → Prop
axiom rel.refl (p : point) : rel p p

axiom congf (α β : Type) (a b : α) (f : α → β) : a = b → f a = f b

-- f = point.x, g = point.y
def helper2 (f g : point → ℕ) (rel : point → point → Prop) := rel.
#check helper2

#print point_destruct''

#check @and.intro
lemma point_destruct'''_1 (p₁ p₂ : point) (h : p₁ = p₂) :
  p₁.x = p₂.x ∧ p₁.y = p₂.y := by {
    apply eq.subst h,
    apply and.intro,
    repeat { exact eq.refl _, },
  }

lemma point_destruct'''_2 (p₁ p₂ : point) (h : p₁ = p₂) :
  p₁.x = p₂.x ∧ p₁.y = p₂.y := h ▸ (and.intro rfl rfl)

-- example of "meta test driven development" and simple: what is operator ▸ ?
-- example (h X : Prop) : h ▸ X = eq.subst h X := sorry 

  -- (λ h₂, and.intro h₂ h₂) (point_arg h)

  -- by {
  --   apply helper,
  --   apply point_arg h,
  --   apply point_arg h,
  -- }

#print point_destruct'''

/-
λ (p₁ p₂ : point) (h : p₁ = p₂),
  ⟨(λ (c c_1 : point) (e_1 : c = c_1), congr_arg point.x e_1) p₁ p₂ h,
   (λ (c c_1 : point) (e_1 : c = c_1), congr_arg point.y e_1) p₁ p₂ h⟩
-/

-- Π {C : point → Sort ?} (n : point), (Π (x y : ℕ), C {x := x, y := y}) → C n
example : Prop = Sort 0 := rfl

example (a b c : ℕ) : a * b + b * c = b * (a + c) := by {
  have distrib : ∀ a b c : ℕ, a * (b + c) = a * b + a * c := sorry,
  have add_assoc : ∀ a b c : ℕ, a + (b + c) = (a + b) + c := sorry,
  have mul_assoc : ∀ a b c : ℕ, a * (b * c) = (a * b) * c := sorry,
  have add_comm : ∀ a b : ℕ, a + b = b + a := sorry,
  have mul_comm : ∀ a b : ℕ, a * b = b * a := sorry,
  have mul_zero : ∀ a : ℕ, a * 0 = 0 := sorry,
  
  sorry,
}