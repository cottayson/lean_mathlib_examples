import data.matrix.notation

example (x : ℕ) (h : x = 3) : x + x + x = 9 :=
begin
  set y := x with ←h_xy,
  guard_hyp y := ℕ,
  guard_hyp h_xy := x = y,
  guard_hyp h := y = 3,
  guard_target y + y + y = 9,
  set! z : ℕ := y,
  guard_target y + y + y = 9, -- target stay the same
  simp [h],
end