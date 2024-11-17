import Mathlib
import FilteredRing.Basic
import FilteredRing.filtered_category

variable {R : Type u} {ι : Type v} [CommSemiring R] [OrderedAddCommMonoid ι] [DecidableEq ι]
  {σ : Type o} [SetLike σ R] [AddSubmonoidClass σ R] (F : ι → σ) [FilteredRing F]

variable (M : Type*) [AddCommGroup M] [Module R M] {σM : Type*} [SetLike σM M] [AddSubgroupClass σM M]
variable (N : Type*) [AddCommGroup N] [Module R N] {σN : Type*} [SetLike σN N] [AddSubgroupClass σN N]
variable (FM : ι → σM) (FN : ι → σN) [FilteredModule F FM] [FilteredModule F FN]

open DirectSum TensorProduct

def indices (i : ι) := {x : ι × ι // x.1 + x.2 = i}

instance FilteredPiece (i : ι) : Submodule ℤ (M ⊗[ℤ] N) where
  carrier := ⨆ x : indices i, LinearMap.range (mapIncl (AddSubgroup.toIntSubmodule (AddSubmonoidClass.subtype (FM x.1.1)).range) (AddSubgroup.toIntSubmodule (AddSubmonoidClass.subtype (FN x.1.2)).range))
  add_mem' := sorry
  zero_mem' := sorry
  smul_mem' := sorry



-- instance tensor_filtration : FilteredModule F FilteredPiece where
