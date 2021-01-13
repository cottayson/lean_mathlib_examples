import tactic.nth_rewrite
import data.vector

structure F :=
(a : ℕ)
(v : vector ℕ a)
(p : v.val = [])

example (f : F) : f.v.val = [] := by nth_rewrite 0 [f.p]

structure cat :=
  (O : Type) -- Type of objects
  (H : O → O → Type) -- morphisms (arrows) between objects
  (i : Π o : O, H o o) -- identity morphism
  (c : Π {X Y Z : O} (f : H X Y) (g: H Y Z), H X Z) 
  -- if exists X → Y and Y → Z then exists X → Z
  (li : Π {X Y : O} (f : H X Y), c (i X) f = f) -- id ∘ f = f
  (ri : Π {X Y : O} (f : H X Y), c f (i Y) = f) -- f ∘ id = f
  (a : Π {W X Y Z : O} (f : H W X) (g : H X Y) (h : H Y Z), c (c f g) h = c f (c g h))
  -- associativity of morphisms composition: (f ∘ g) ∘ h = f ∘ (g ∘ h)

open tactic

example (C : cat) (W X Y Z : C.O) (f : C.H X Y) (g : C.H W X) (h k : C.H Y Z) :
  C.c (C.c g f) h = C.c g (C.c f h) := by nth_rewrite 0 [C.a] -- rw C.a, OK

example (C : cat) (X Y : C.O) (f : C.H X Y) : C.c f (C.i Y) = f := by nth_rewrite 0 [C.ri]

example (a b : ℕ) (h : b = a) (H : a * a = b * b) : 
  b * a = a * a ∧ a * b = a * a :=
begin
  have h₀ := H, have h₁ := H, have h₂ := H, have h₃ := H,
  nth_rewrite 0 h at h₀,     nth_rewrite 1 h at h₁,
  rw h₁,
  split; simp [h₀, h₁] {fail_if_unchanged := ff},
  simp [h₀, ←h₁],
end

axiom foo : [1] = [2]

example : [[1], [1], [1]] = [[2], [1], [2]] := by {
  nth_rewrite_lhs 0 [foo], -- lhs means left part of an equation
  nth_rewrite_lhs 1 [foo], -- rhs means right part of an equation
}

axiom foo' : [6] = [7]
axiom bar' : [[5], [5]] = [[6], [6]]

lemma ex1 : [[7], [6]] = [[5], [5]] := by {
  nth_rewrite_lhs 0 foo',
  nth_rewrite_rhs 0 bar',
  nth_rewrite_lhs 0 ←foo',
  nth_rewrite_lhs 0 ←foo',
}

#print ex1

-- example backtracking
example (a b c : ℕ) : c + a + b = a + c + b := by {
  -- nth_rewrite_lhs 0 add_comm, -- not solved next try
  -- nth_rewrite_lhs 1 add_comm, -- solved, but we want to find all solutions
  -- start
  nth_rewrite_lhs 0 add_comm,
  nth_rewrite_lhs 0 add_comm, -- this two lines doing nothing => delete branch
  -- start
  nth_rewrite_lhs 0 add_comm,
  nth_rewrite_lhs 1 add_comm,
  -- nth_rewrite 1 add_comm, -- do nothing => delete branch
  nth_rewrite_lhs 0 add_comm, -- solved with 3 rewrites
}

