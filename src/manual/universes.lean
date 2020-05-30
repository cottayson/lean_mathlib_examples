-- lean_reference.pdf Chapter THREE
-- Universes
namespace ex1
universes u v
#check Sort u
#check Sort 5
#check Sort (u + 1)
#check Sort (u + 3)
#check Sort (max (u + 3) v)
#check Sort (imax (u + 3) v)
#check Prop
#check Type
#check Type 1

end ex1

-- Sort u : the universe of types at universe level u
-- c : where c is an identifier denoting an axiomatically declared constant or a defined object
-- x : where x is a variable in the local context in which the expression is interpreted
-- Π x : α, β : the type of functions taking an element x of α to an element of β, there β is an expression whose type is a Sort
-- s t : the result of applying s to t, where s and t are expressions
-- λ x : α, t : the function mapping any value x of type α to t, where t is an expression
-- let x := t in s : a local definition, denotes the value of s when x is replaced by t

/-
Every well founded term in Lean has a type, which itself is an expression of type Sort u for some u.
The fact that a term t has type α is written t : α.

For an expression to be well formed, its components have to satisfy certain typing constants.
These, in turn, determine the type of the resulting term, as follows:
  * Sort u : Sort (u + 1)
  * c : α, where α is the type that c has been declared or defined to have
  * x : α, where α is the type that x has been assigned in the local context where it is interpreted
  * (Π x : α, β) : Sort (imax u v) where α : Sort u, and β : Sort v assuming x : α
  * s t : β[t/x] where s has type Π x : α, β and t has type α
  * (λ x : α, t) : Π x : α, β if t has type β whenever x has type α
  * (let x := t in s) : β[t/x] where t has type α and s has type β assuming x : α

Prop abbreviates Sort 0,
Type abbreviates Sort 1, and
Type u abbreviates Sort (u + 1)
  when u is a universe variable.
-/

namespace ex2

universes u v w

variables (p q : Prop)
variable  (α : Type u)
variable  (β : Type v)
variable  (γ : α → Type w)
variable  (η : α → β → Type w)

constants δ ε : Type u
constants cnst : δ
constant f : δ → ε

variables (a : α) (b : β) (c : γ a) (d : δ)

variable  g  : α → β
variable  h  : Π x : α, γ x
variable  h' : Π x, γ x → δ

#check Sort (u + 3) -- Type (u+2) : Type (u+3)
#check Prop -- Prop : Type
#check Π x : α, γ x -- Π (x : α), γ x : Type (max u w)
#check f cnst -- f cnst : ε
#check λ x, h x -- λ (x : α), h x : Π (x : α), γ x
#check λ x, h' x (h x) -- λ (x : α), h' x (h x) : α → δ
#check (λ x, h x) a -- (λ (x : α), h x) a : γ a
#check λ _ : ℕ, 5 -- λ (_x : ℕ), 5 : ℕ → ℕ
#check let x := a in h x -- let x : α := a in h x : γ a

end ex2