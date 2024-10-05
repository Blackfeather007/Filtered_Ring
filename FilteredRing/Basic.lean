import Mathlib

universe u v

open Pointwise

variable (R : Type u) (ι : Type v) [Ring R] [OrderedAddCommMonoid ι] [DecidableEq ι]

class FilteredRing where
  fil : ι → AddSubgroup R
  mono : ∀ i ≤ j, fil i ≤ fil j
  one : 1 ∈ fil 0
  mul_mem : ∀ i j : ι, (fil i : Set R) * fil j ≤ fil (i + j)

variable [F : FilteredRing R ι]
variable (M : Type u) [AddCommGroup M] [Module R M]

class FilteredModule where
  fil : ι → Submodule R M
  mono : ∀ i ≤ j, fil i ≤ fil j
  smul_mem : ∀ i j, (F.fil i : Set R) • fil j ≤ fil (i + j)
