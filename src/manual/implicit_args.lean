/- 3.3 Implicit Arguments
  * (x : α) : an explicit argument of type α
  * {x : α} : an implicit argument, eagerly inserted
  * ⦃x : α⦄ or {{x : α}} : an implicit argument, weakly inserted
  * [x : α] : implicit argument that should be inferred by type class resolution
  * (x : α := t) : an optional argument, with default value t
  * (x : α . t) : an implicit argument, to be synthesized by tactic t
-/
namespace args
universe u

def ex1 (x y z : ℕ) : ℕ := x + y + z
#check ex1 1 2 3 -- ex1 1 2 3 : ℕ

def id1 (α : Type u) (x : α) : α := x

#check id1 nat 3 -- id1 ℕ 3 : ℕ
#check id1 _ 3   -- id1 ℕ 3 : ℕ

-- id with implicit arguments
def id2 {α : Type u} (x : α) : α := x

#check id2 3     -- id2 3 : ℕ
#check @id2 ℕ 3 -- id2 3 : ℕ
#check (id2 : ℕ → ℕ) -- OK

def id3 {{α : Type u}} (x : α) : α := x

#check id3 3     -- id2 3 : ℕ
#check @id3 ℕ 3 -- id2 3 : ℕ
-- #check (id3 : ℕ → ℕ) -- invalid type ascription, term has type
--   Π ⦃α : Type ?⦄, α → α : Type (?+1)
-- but is expected to have type
--   ℕ → ℕ : Type
#check (id3 : Π α : Type, α → α) -- OK

class cls := (val : ℕ)
instance cls_five : cls := ⟨5⟩

#check cls_five -- cls_five : cls
#reduce cls_five -- {val := 5}

def ex2 [c : cls] : ℕ := c.val
#reduce ex2 -- 5

def ex2a [c : cls] : ℕ := ex2
#reduce ex2a -- 5

def ex3 (x : ℕ := 5) := x
#check ex3 2 -- ex3 2 : opt_param ℕ 5
#check ex3 -- ex3 : opt_param ℕ 5
#reduce ex3 -- 5
example : ex3 = 5 := rfl

meta def ex_tac : tactic unit := tactic.refine ``(5)

def ex4 (x : ℕ . ex_tac) := x
#reduce ex4 -- 5

end args
/- 3.5 Constructors, Projections, and Matching -/
namespace constructors

universes u v

variables {α : Type u} {β : Type v}
def p : ℕ × ℤ := ⟨1, 2⟩
#check p.fst -- ℕ
#check p.snd -- ℤ

def p' : ℕ × ℤ × bool := ⟨1, 2, tt⟩
#check p'.fst -- ℕ
#check p'.snd.fst -- ℤ
#check p'.snd.snd -- bool

def swap_pair (p : α × β) : β × α :=
⟨p.snd, p.fst⟩

theorem swap_conj {a b : Prop} (h : a ∧ b) : b ∧ a :=
⟨h.right, h.left⟩

#reduce [1, 2, 3].append [2, 3, 4] -- [1, 2, 3, 2, 3, 4] : list ℕ
#reduce [1, 2, 3].map (λ x, x^2) -- [1, 4, 9] : list ℕ

example (p q : Prop) : p ∧ q → q ∧ p :=
λ h, ⟨h.right, h.left⟩

def swap_pair' (p : α × β) : β × α :=
let (x, y) := p in (y, x)

theorem swap_conj' {a b : Prop} (h : a ∧ b) : b ∧ a :=
let ⟨ha, hb⟩ := h in ⟨hb, ha⟩

def swap_pair'' : α × β → β × α :=
λ ⟨x, y⟩, (y, x)

theorem swap_conj'' {a b : Prop} : a ∧ b → b ∧ a :=
assume ⟨ha, hb⟩, ⟨hb, ha⟩

end constructors