-- source: https://github.com/bryangingechen/lean-fibonacci/blob/master/src/fib.lean
import data.list.range


@[reducible]
def fibonacci : ℕ → ℕ
| 0 := 0
| 1 := 1
| (n+2) := fibonacci n + fibonacci (n+1)

open nat list

@[reducible]
def fib_sum (n : ℕ) : ℕ :=
  ((range n).map fibonacci).sum

@[reducible]
def fib_odd_sum (n : ℕ) : ℕ :=
  ((range n).map (λ m, fibonacci (2*m + 1))).sum

@[reducible]
def fib_even_sum (n : ℕ) : ℕ :=
  ((range n).map (λ m, fibonacci (2*m))).sum

theorem fib_odd_sum_eq : ∀ (n : ℕ),
  fib_odd_sum n = fibonacci (2*n)
| 0 := rfl
| (n+1) := by rw [
    fib_odd_sum,
    sum_range_succ, -- (f : ℕ → α) (n : ℕ), (map f (range n.succ)).sum = (map f (range n)).sum + f n
    ←fib_odd_sum,
    fib_odd_sum_eq,
    mul_add, -- (a b c : α), a * (b + c) = a * b + a * c
    mul_one, -- (a : α), a * 1 = a
    fibonacci
  ]

theorem fib_even_sum_eq : ∀ {n : ℕ} (h : n > 0),
  fib_even_sum n + 1 = fibonacci (2*n - 1)
| 0 h := (gt_irrefl 0 h).elim -- used false.elim : false → C
| 1 _ := rfl
| (n+2) _ :=
have H : fib_even_sum (n+1) + 1 = fibonacci (2*(n+1) - 1) :=
  fib_even_sum_eq (succ_pos n),
begin
  rw [fib_even_sum,
    sum_range_succ,
    ←fib_even_sum,
    add_right_comm,
    H,
    mul_add,
    mul_one,
    mul_add],
  change fibonacci (2*n + 1) + fibonacci (2*n + 1 + 1) =
    fibonacci (2*n + 1 + 2),
  rw [←fibonacci],
end
-- *** Added example ***
namespace false_elim_test

constant h1 : false
#check false.elim h1
#check @false.elim

end false_elim_test

set_option trace.simplify.rewrite true

theorem fib_sum_eq : ∀ (n : ℕ),
  fib_sum n + 1 = fibonacci (n+1)
| 0 := rfl
| (n+1) :=
begin
  rw [fibonacci,
    ←fib_sum_eq n
  ],
  simp [range_concat, fib_sum, add_left_comm, add_comm],
-- [fib_sum.equations._eqn_1]: fib_sum (n + 1) ==> (map fibonacci (range (n + 1))).sum
-- [list.range_concat]: range (n + 1) ==> range n ++ [n]
-- [list.map_append]: map fibonacci (range n ++ [n]) ==> map fibonacci (range n) ++ map fibonacci [n]
-- [list.map.equations._eqn_2]: map fibonacci [n] ==> fibonacci n :: map fibonacci nil
-- [list.map_nil]: map fibonacci nil ==> nil
-- [list.sum_append]: (map fibonacci (range n) ++ [fibonacci n]).sum ==> (map fibonacci (range n)).sum + [fibonacci n].sum
-- [list.sum_cons]: [fibonacci n].sum ==> fibonacci n + nil.sum
-- [list.sum_nil]: nil.sum ==> 0
-- [add_zero]: fibonacci n + 0 ==> fibonacci n
-- [add_comm]: (map fibonacci (range n)).sum + fibonacci n ==> fibonacci n + (map fibonacci (range n)).sum
-- [add_comm]: fibonacci n + (map fibonacci (range n)).sum + 1 ==> 1 + (fibonacci n + (map fibonacci (range n)).sum)
-- [add_left_comm]: 1 + (fibonacci n + (map fibonacci (range n)).sum) ==> fibonacci n + (1 + (map fibonacci (range n)).sum)
-- [fib_sum.equations._eqn_1]: fib_sum n ==> (map fibonacci (range n)).sum
-- [add_comm]: (map fibonacci (range n)).sum + 1 ==> 1 + (map fibonacci (range n)).sum
-- [add_left_inj]: fibonacci n + (1 + (map fibonacci (range n)).sum) = fibonacci n + (1 + (map fibonacci (range n)).sum) ==> fibonacci n = fibonacci n
-- [eq_self_iff_true]: fibonacci n = fibonacci n ==> true
end

inductive bee : Type
| queen : bee
| worker : bee
| drone : bee

open bee list

instance : has_repr bee :=
⟨λ s, match s with
| queen := "Q"
| worker := "W"
| drone := "D"
end⟩

namespace bee

def parents : bee → list bee
| queen := [queen, drone]
| worker := [queen, drone]
| drone := [queen]

def ancestors (b : bee) : ℕ → list bee
| 0 := [b]
| (n+1) := ((ancestors n).map parents).join

def tree_json : bee → ℕ → string
| b 0 := "{\"name\":\"" ++ repr b ++ "\"}"
| b (n+1) := "{\"name\":\"" ++ repr b ++ "\",\"children\":[" ++
  string.intercalate "," (b.parents.map (λ p, p.tree_json n)) ++ "]}"

lemma drone_ancestors_concat : ∀ (n : ℕ),
  drone.ancestors (n+2) = drone.ancestors (n+1) ++ drone.ancestors n
| 0 := rfl
| (n+1) := begin
  change ((ancestors _ (n+2)).map _).join = _,
  conv {
    to_lhs,
    rw [
      drone_ancestors_concat n,
      map_append, -- (f : α → β) (l₁ l₂ : list α), map f (l₁ ++ l₂) = map f l₁ ++ map f l₂
      join_append], -- (L₁ L₂ : list (list α)), (L₁ ++ L₂).join = L₁.join ++ L₂.join
  },
  refl,
end

theorem drone_ancestors_length_eq_fib_succ : ∀ (n : ℕ),
  (drone.ancestors n).length = fibonacci (n + 1)
| 0 := rfl
| 1 := rfl
| (n+2) := begin
  rw [
    drone_ancestors_concat,
    length_append, -- (s t : list α), (s ++ t).length = s.length + t.length
    drone_ancestors_length_eq_fib_succ n,
    drone_ancestors_length_eq_fib_succ (n+1),
    add_comm -- (a b : α), a + b = b + a
  ],
  refl,
end

end bee
---
inductive car : Type
| rabbit : car
| cadillac : car

open car list nat

instance : has_repr car :=
⟨λ s, match s with
| rabbit := "R"
| cadillac := "C"
end⟩

namespace car

@[reducible]
def size : car → ℕ
| rabbit := 1
| cadillac := 2

@[reducible]
def sum_size (cs : list car) : ℕ :=
  (cs.map size).sum

lemma sum_size_cons (c : car) (cs : list car) :
  sum_size (c :: cs) = sum_size cs + c.size :=
begin
  simp only [sum_size, sum_cons, map, add_comm],
  -- [car.sum_size.equations._eqn_1]: sum_size (c :: cs) ==> (map size (c :: cs)).sum
  -- [list.map.equations._eqn_2]: map size (c :: cs) ==> c.size :: map size cs
  -- [list.sum_cons]: (c.size :: map size cs).sum ==> c.size + (map size cs).sum
  -- [car.sum_size.equations._eqn_1]: sum_size cs ==> (map size cs).sum
  -- [add_comm]: (map size cs).sum + c.size ==> c.size + (map size cs).sum 
end

@[reducible]
def packings : ℕ → list (list car)
| 0 := [[]]
| 1 := [[rabbit]]
| (n+2) := (packings (n+1)).map (cons rabbit) ++
  (packings n).map (cons cadillac)

theorem num_packings_eq_fib : ∀ (n : ℕ),
  (packings n).length = fibonacci (n+1)
| 0 := rfl
| 1 := rfl
| (n+2) :=
begin
  simp [packings, fibonacci, add_left_comm, add_comm],
  -- [car.packings.equations._eqn_3]: packings (n + 2) ==> map (cons rabbit) (packings n.succ) ++ map (cons cadillac) (packings n)
  -- [list.length_append]: (map (cons rabbit) (packings n.succ) ++ map (cons cadillac) (packings n)).length ==> (map (cons rabbit) (packings n.succ)).length + (map (cons cadillac) (packings n)).length
  -- [list.length_map]: (map (cons rabbit) (packings n.succ)).length ==> (packings n.succ).length
  -- [list.length_map]: (map (cons cadillac) (packings n)).length ==> (packings n).length
  -- [add_comm]: (packings n.succ).length + (packings n).length ==> (packings n).length + (packings n.succ).length
  -- [add_comm]: n + 2 + 1 ==> 1 + (n + 2)
  -- [add_left_comm]: 1 + (n + 2) ==> n + (1 + 2)
  -- [add_zero]: n + (1 + 2) ==> n + 3
  -- [fibonacci.equations._eqn_3]: fibonacci (n + 3) ==> fibonacci (n + 1) + fibonacci (n + 1).succ
  -- [fibonacci.equations._eqn_3]: fibonacci (n + 1).succ ==> fibonacci n + fibonacci n.succ
  -- [add_left_comm]: fibonacci (n + 1) + (fibonacci n + fibonacci n.succ) ==> fibonacci n + (fibonacci (n + 1) + fibonacci n.succ)
  -- [add_comm]: fibonacci (n + 1) + fibonacci n.succ ==> fibonacci n.succ + fibonacci (n + 1)
  rw [num_packings_eq_fib n,
    num_packings_eq_fib (n+1),
    add_left_comm, -- (a b c : α), a + (b + c) = b + (a + c)
    add_right_inj, -- (a : M) {b c : M}, a + b = a + c ↔ b = c
    fibonacci
  ],
end

theorem packing_size : ∀ {n : ℕ} {cs : list car} (h : cs ∈ packings n),
  sum_size cs = n
| 0 cs h :=
begin
  rw mem_singleton.1 h,
  refl,
end
| 1 cs h :=
begin
  rw mem_singleton.1 h,
  refl,
end
| (n+2) cs h :=
begin
  simp [packings] at h,
-- [car.packings.equations._eqn_3]: packings (n + 2) ==> 
--                                    map (cons rabbit) (packings n.succ) ++ map (cons cadillac) (packings n)
-- [list.mem_append]: cs ∈ map (cons rabbit) (packings n.succ) ++ map (cons cadillac) (packings n) ==>
--                      cs ∈ map (cons rabbit) (packings n.succ) ∨ cs ∈ map (cons cadillac) (packings n)
-- [list.mem_map]: cs ∈ map (cons rabbit) (packings n.succ) ==> 
--                   ∃ (a : list car), a ∈ packings n.succ ∧ rabbit :: a = cs
-- [list.mem_map]: cs ∈ map (cons cadillac) (packings n) ==> 
--                   ∃ (a : list car), a ∈ packings n ∧ cadillac :: a = cs
  rcases h with ⟨cs', h₁, h₂⟩ | ⟨cs', h₁, h₂⟩,
  all_goals {
    rw [
      ←h₂,
      sum_size_cons,
      size,
      packing_size h₁
    ],
  },
end

lemma car_size_ne_zero (c : car) : size c ≠ 0 :=
by cases c; contradiction -- why contradiction tactic works with ⊢ rabbit.size ≠ 0 ?

lemma sum_size_zero : ∀ {cs : list car} (h : sum_size cs = 0),
  cs = []
| [] _ := rfl
| (c :: cs) h :=
begin -- ⊢ c :: cs = nil
  exfalso, -- try to find contradiction
  rw [
    sum_size_cons, -- sum_size (c :: cs) = sum_size cs + c.size
    add_eq_zero_iff -- a + b = 0 ↔ a = 0 ∧ b = 0
  ] at h,
  apply car_size_ne_zero c,
  exact h.right,
end

lemma sum_size_one : ∀ {cs : list car} (h : sum_size cs = 1),
  cs = [rabbit]
| [] h := by contradiction -- ⊢ nil = [rabbit]
| (rabbit :: cs) h :=
begin
  rw sum_size_cons at h, -- sum_size (c :: cs) = sum_size cs + c.size
  simp,
  -- [eq_self_iff_true]: rabbit = rabbit ==> true
  -- [true_and]: true ∧ cs = nil ==> cs = nil

  -- ⊢ cs = nil
  apply sum_size_zero, -- sum_size cs = 0 → cs = nil
  -- ⊢ sum_size cs = 0
  have u := succ_inj h, -- succ_inj : n.succ = m.succ → n = m
  change sum_size cs + 1 = 1 at h, -- rabbit.size = 1
  exact u, 
end
| (cadillac :: cs) h :=
begin
  rw sum_size_cons at h, -- sum_size (c :: cs) = sum_size cs + c.size
  have : sum_size cs + 1 = 0 := succ_inj h,
  -- cadillac.size = 2
  rw size at h,
  contradiction, -- why contradiction works ?
end

theorem all_packings : ∀ {n : ℕ} {cs : list car} (h : sum_size cs = n),
  cs ∈ packings n
| 0 cs h := by simp [packings, sum_size_zero h]
| 1 cs h := by simp [packings, sum_size_one h]
| (n+2) [] h := by contradiction -- this case have 0 solutions?
| (n+2) (rabbit :: cs) h :=
begin
  rw [sum_size_cons, -- sum_size (c :: cs) = sum_size cs + c.size
    add_left_inj 1 -- (a : M) {b c : M}, b + a = c + a ↔ b = c
  ] at h,
  simp [packings, all_packings, h],
  -- [car.packings.equations._eqn_3]: packings (n + 2) ==> map (cons rabbit) (packings n.succ) ++ map (cons cadillac) (packings n)
  -- [list.mem_append]: rabbit :: cs ∈ map (cons rabbit) (packings n.succ) ++ map (cons cadillac) (packings n) ==>
  --                      rabbit :: cs ∈ map (cons rabbit) (packings n.succ) ∨ rabbit :: cs ∈ map (cons cadillac) (packings n)
  -- [list.mem_map]: rabbit :: cs ∈ map (cons rabbit) (packings n.succ) ==> 
  --                             ∃ (a : list car), a ∈ packings n.succ ∧ rabbit :: a = rabbit :: cs
  -- [eq_self_iff_true]: rabbit = rabbit ==> true
  -- [true_and]: true ∧ a = cs ==> a = cs
  -- [exists_eq_right]: ∃ (a : list car), a ∈ packings n.succ ∧ a = cs ==> cs ∈ packings n.succ
  -- [h]: sum_size cs ==> n + 1
  -- [eq_self_iff_true]: n + 1 = n.succ ==> true
  -- [[anonymous]]: cs ∈ packings n.succ ==> true
  -- [list.mem_map]: rabbit :: cs ∈ map (cons cadillac) (packings n) ==> ∃ (a : list car), a ∈ packings n ∧ cadillac :: a = rabbit :: cs
  -- [false_and]: false ∧ a = cs ==> false
  -- [and_false]: a ∈ packings n ∧ false ==> false
  -- [exists_false]: ∃ (a : list car), false ==> false
  -- [or_false]: true ∨ false ==> true
end
| (n+2) (cadillac :: cs) h :=
begin
  rw [sum_size_cons,
    add_left_inj 2] at h,
  simp [packings, all_packings, h],
end

end car