import Mathlib
import FilteredRing.Basic

set_option maxHeartbeats 0

variable {R : Type u} {ι : Type v} [CommSemiring R] [OrderedAddCommGroup ι] [DecidableEq ι]
  {σ : Type o} [SetLike σ R] [AddSubmonoidClass σ R] (F : ι → σ) [FilteredRing F]

variable {M : Type*} [AddCommGroup M] [Module R M] {σM : Type*} [SetLike σM M] [AddSubgroupClass σM M]
variable {N : Type*} [AddCommGroup N] [Module R N] {σN : Type*} [SetLike σN N] [AddSubgroupClass σN N]
variable (FM : ι → σM) (FN : ι → σN) [filM : FilteredModule F FM] [filN : FilteredModule F FN]

open DirectSum TensorProduct Pointwise

def indices (i : ι) := {x : ι × ι // x.1 + x.2 = i}

noncomputable def FilteredPiece (i : ι) : Submodule ℤ (M ⊗[ℤ] N) := ⨆ x : indices i, LinearMap.range
  (mapIncl (AddSubgroup.toIntSubmodule (AddSubmonoidClass.subtype (FM x.1.1)).range)
  (AddSubgroup.toIntSubmodule (AddSubmonoidClass.subtype (FN x.1.2)).range))






instance tensor_filtration : FilteredModule F (FilteredPiece FM FN) where
  mono := by
    simp only [FilteredPiece, TensorProduct.range_mapIncl]
    intro i j ilej
    apply iSup_le; intro x
    apply Submodule.span_le.2
    simp only [AddSubgroup.coe_toIntSubmodule, AddMonoidHom.coe_range,
      AddSubmonoidClass.coe_subtype, Subtype.range_coe_subtype, Set.image2_subset_iff,
      Set.mem_setOf_eq, SetLike.mem_coe]
    intro m hm n hn
    refine Submodule.mem_iSup_of_mem ⟨(x.1.1, j - i + x.1.2), by rw [add_comm, add_assoc,
      add_comm x.1.2, x.2, sub_add_cancel]⟩ (Set.mem_of_subset_of_mem Submodule.subset_span ?_)
    use m, hm, n, (by apply filN.mono (by simp only [le_add_iff_nonneg_left, sub_nonneg, ilej]) hn)
  smul_mem := by
    intro i j x y hx hy
    have : x • y ∈ x • (FilteredPiece FM FN j) :=
      Submodule.smul_mem_pointwise_smul y x (FilteredPiece FM FN j) hy
    refine SetLike.mem_of_subset (SetLike.coe_subset_coe.mpr ?_) this

    simp only [vadd_eq_add, FilteredPiece]


    -- simp only [vadd_eq_add, FilteredPiece, TensorProduct.range_mapIncl,
    --   AddSubgroup.coe_toIntSubmodule, AddMonoidHom.coe_range, AddSubmonoidClass.coe_subtype,
    --   Subtype.range_coe_subtype]
