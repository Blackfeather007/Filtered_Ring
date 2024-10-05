import Mathlib

universe u v

open Pointwise

variable (R : Type u) [Ring R]

class FilteredRing where
  fil : ℤ → AddSubgroup R
  mono : ∀ i : ℤ, fil i ≤ fil (i + 1)
  one : 1 ∈ fil 0
  mul_mem : ∀ i j : ℤ, (fil i : Set R) * fil j ≤ fil (i + j)

variable [F : FilteredRing R]
variable (M : Type u) [AddCommGroup M] [Module R M]

class FilteredModule where
  fil : ℤ → Submodule R M
  mono : ∀ i : ℤ, fil i ≤ fil (i + 1)
  smul_mem : ∀ i j, (F.fil i : Set R) • fil j ≤ fil (i + j)
