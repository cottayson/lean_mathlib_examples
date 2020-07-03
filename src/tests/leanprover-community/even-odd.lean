-- https://github.com/leanprover-community/lean/blob/ec1613aef1eee72e601f192b16740629c6d49690/tmp/even_odd.lean

import data.vector
open nat
universes u v

-- set_option trace.eqn_compiler.wf_rec true
set_option trace.debug.eqn_compiler.wf_rec true
-- set_option trace.debug.eqn_compiler.mutual true

mutual def even, odd
with even : nat → bool
| 0     := tt
| (a+1) := odd a
with odd : nat → bool
| 0     := ff
| (a+1) := even a

#print even
#print even._main
-- #print _mutual.even.odd -- unknown identifier _mutual.even.odd

#eval even 3 -- ff
#eval even 4 -- tt
#eval odd 3 -- tt
#eval odd 4 -- ff
#check even.equations._eqn_1 -- even 0 = tt
#check even.equations._eqn_2 -- ∀ (a : ℕ), even (a + 1) = odd a
#check odd.equations._eqn_1 -- odd 0 = ff
#check odd.equations._eqn_2 -- ∀ (a : ℕ), odd (a + 1) = even a

mutual def f, g {α β : Type u} (p : α × β)
with f : Π n : nat, vector (α × β) n
| 0        := vector.nil
| (succ n) := vector.cons p $ (g n p.1).map (λ b, (p.1, b))
with g : Π n : nat, α → vector β n
| 0        a := vector.nil
| (succ n) a := vector.cons p.2 $ (f n).map (λ p, p.2)

#check @f.equations._eqn_1 -- ∀ {α β : Type u_1} (p : α × β), f p 0 = vector.nil
#check @f.equations._eqn_2 
-- ∀ {α β : Type u_1} (p : α × β) (n : ℕ), 
  -- f p n.succ = p :: vector.map (λ (b : β), (p.fst, b)) (g p n p.fst)
#check @g.equations._eqn_1 -- ∀ {α β : Type u_1} (p : α × β) (a : α), g p 0 a = vector.nil
#check @g.equations._eqn_2
-- ∀ {α β : Type u_1} (p : α × β) (n : ℕ) (a : α), 
  -- g p n.succ a = p.snd :: vector.map (λ (p : α × β), p.snd) (f p n)