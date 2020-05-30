section monad_example

def action (σ α : Type) :=
σ → α × σ

def action.read {σ : Type} : action σ σ
| s := (s, s)

def action.write {σ : Type} (s : σ) : action σ unit
| _ := ((), s)

def action.pure {σ α : Type} (a : α) : action σ α
| s := (a, s)

def action.bind {σ : Type} {α β : Type} (ma : action σ α)
    (f : α → action σ β) :
  action σ β
| s :=
  match ma s with
  | (a, s') := f a s'
  end

def diff_list : list ℕ → action ℕ (list ℕ)
| [] := pure []
| (n :: ns) :=
  do
    prev ← action.read,
    if n < prev then
      diff_list ns
    else
      do
        action.write n,
        ns' ← diff_list ns,
        pure (n :: ns')

end monad_example