import Mathlib
import FilteredRing.Basic
import FilteredRing.filtered_category

variable {R : Type u} {ι : Type v} [Ring R] [OrderedAddCommMonoid ι] {σ : Type o} [SetLike σ R]
  (F : ι → σ) [FilteredRing F]

variable (M : Type*) [AddCommMonoid M] [Module R M] {σM : Type*} [SetLike σM M] [AddSubmonoidClass σM M]
variable (N : Type*) [AddCommMonoid N] [Module R N] {σN : Type*} [SetLike σN N] [AddSubmonoidClass σN N]
variable (FM : ι → σM) (FN : ι → σN) [FilteredModule F FM] [FilteredModule F FN]
