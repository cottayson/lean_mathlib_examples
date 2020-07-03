/-
L1 : sin² α + cos² α = 1
tg.def : tg α = sin α / cos α
tg.def₂ : tg α * cos α = sin α

⊢ cos² α = 1 / (1 + tg² α)
we have:
sin² α + cos² α = 1, from L1
=> (tg α * cos α)² + cos² α = 1, by tg.def₂
=> (tg² α + 1) * cos² α = 1, by arith_set_of_aksioms
=> show cos² α = 1 / (tg² α + 1), by arith_set_of_aksioms
=> Q. E. D. (if add.comm, eq.symm, etc.. ≈ identity)
-/