import Mathlib

universe u v w

variable {R : Type u} {ι : Type v} [Ring R] [OrderedAddCommMonoid ι]

class FilteredRing (F : ι → AddSubgroup R) where
  mono : ∀ i ≤ j, F i ≤ F j
  one : 1 ∈ F 0
  mul_mem : ∀ {i j x y}, x ∈ F i → y ∈ F j → x * y ∈ F (i + j)

variable (F : ι → AddSubgroup R) [FilteredRing F]
variable (M : Type w) [AddCommGroup M] [Module R M]

class FilteredModule (F' : ι → Submodule R M) where
  mono : ∀ i ≤ j, F' i ≤ F' j
  smul_mem : ∀ {i j x y}, x ∈ F i → y ∈ F' j → x • y ∈ F' (i + j)
