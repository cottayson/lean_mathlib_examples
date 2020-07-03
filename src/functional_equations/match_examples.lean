meta def solve (n : nat) (f : nat → nat) :=
match n, f with
| 0, _ := 0
| _, _ := 1
end


def foo (n : nat) (b c : bool) :=
match n - 5, b && c with
| 0, tt := 0
| m+1, tt := m + 7
| 0, ff := 5
| m+1, ff := m + 3
end


def u (x y : nat) :=
match (⟨x, y⟩ : nat × nat) with
| ⟨0, 0⟩ := 0
| ⟨_, _⟩ := 1
end

#reduce u -- λ (x y : ℕ), u._match_1 (x, y)
#reduce u 0 -- λ (y : ℕ), u._match_1 (0, y)
#reduce u 1 -- λ (y : ℕ), 1

def g (n m : nat) :=
match n with
| 0 := 0
| _ := 1
end
#reduce g 0 -- λ (m : ℕ), 0
#reduce g 5 _ -- 1

#print nat.add