import Mathlib.Tactic

noncomputable section

open Module
open LinearMap
open LinearMap (BilinForm)

variable  {k V :Type} [Field k] [AddCommGroup V] [Module k V]
   [Module.Finite k V] [Invertible (2:k)]


example ( v w : V ) (h:(2:k)•v = (2:k)•w) : v = w := by
  have : (2:k) ≠ 0 := by exact two_ne_zero
  exact (MulAction.injective₀ this) h

