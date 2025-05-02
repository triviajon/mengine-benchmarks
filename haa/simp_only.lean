import Std.Tactic
section Test

variable {α : Type}

variable (f : α → α) (g : α → α) (h : α → α → α)
variable (a b c : α)
variable (eq_haa_a : ∀ x y : α, (h x y) = c)

set_option trace.profiler true in
set_option trace.profiler.threshold 0 in
example : (__HAA__) = (c) := by
  simp only [eq_haa_a]
end Test
