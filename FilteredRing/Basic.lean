import Mathlib

universe u v

open Pointwise

variable {R : Type u} {ι : Type v} [Ring R] [OrderedAddCommMonoid ι] [DecidableEq ι]

class FilteredRing (F : ι → AddSubgroup R) where
  mono : ∀ i ≤ j, F i ≤ F j
  one : 1 ∈ F 0
  mul_mem : ∀ i j : ι, (F i : Set R) * F j ≤ F (i + j)

variable (F : ι → AddSubgroup R) [FilteredRing F]
@[simp]
theorem Filtration.mul_mem (i j : ι) : (F i : Set R) * F j ≤ F (i + j) := FilteredRing.mul_mem i j

variable (F : ι → AddSubgroup R)
variable (M : Type u) [AddCommGroup M] [Module R M]

class FilteredModule (F' : ι → Submodule R M) where
  mono : ∀ i ≤ j, F' i ≤ F' j
  smul_mem : ∀ i j, (F i : Set R) • F' j ≤ F' (i + j)
