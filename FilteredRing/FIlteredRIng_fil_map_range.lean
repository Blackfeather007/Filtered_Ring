import Mathlib
import FilteredRing.Basic
import FilteredRing.filtered_category

variable {R : Type*} [Ring R] {ι : Type v} [OrderedCancelAddCommMonoid ι]  [DecidableEq ι]
variable (FR : ι → AddSubmonoid R) [fil : FilteredRing FR]
variable {S : Type*} [Ring S] (f : R →+* S)

def fil_map  : ι → AddSubmonoid S := fun i ↦ AddSubmonoid.map f (FR i)

instance FilteredRing_fil_map_range (f : R →+* S) : FilteredRing (fil_map FR f) where
  mono := by
    intro i j ilej y hy
    obtain ⟨x, x_in, x_eq⟩ : ∃ x ∈ FR i , f x = y := hy
    use x
    simp only [SetLike.mem_coe, (FilteredRing.mono ilej) x_in, x_eq, and_self]
  one := by
    use 1
    simp only [SetLike.mem_coe, FilteredRing.one, map_one, and_self]
  mul_mem := by
    intro i j x y x_in_i y_in_j
    simp only [fil_map, AddSubmonoid.mem_map] at *
    obtain ⟨x₁, x_in, x_eq⟩ := x_in_i
    obtain ⟨y₁, y_in, y_eq⟩ := y_in_j
    use x₁ * y₁
    simp only [FilteredRing.mul_mem x_in y_in, map_mul, x_eq, y_eq, and_self]
