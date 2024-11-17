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


-- {(m : M) ⊗ₜ[ℤ] (n : N) | (m : FM i) (n : FN j)}
instance tmp (i j : ι): AddSubgroup (M ⊗[ℤ] N) where
  carrier := (FM i) ⊗[ℤ] (FN j)
  add_mem' := by
    intro a b ha hb
  zero_mem' := sorry
  neg_mem' := sorry

-- instance FilteredPiece (i : ι) : AddSubgroup (M ⊗[ℤ] N) where
--   carrier := ⨆ (x : (indices i)), (FM x.1.1) ⊗[ℤ] (FN x.1.2)



-- ⨁ (x : indices i), (FM x.1.1) ⊗[ℤ] (FN x.1.2)

-- instance tensor_filtration : FilteredModule F FilteredPiece where
