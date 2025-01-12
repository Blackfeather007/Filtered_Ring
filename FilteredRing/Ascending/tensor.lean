import FilteredRing.Basic

variable {R : Type u} {ι : Type v} [CommSemiring R] [OrderedAddCommGroup ι] [DecidableEq ι]
  {σ : Type o} [SetLike σ R] [AddSubmonoidClass σ R] (F : ι → σ)(F_lt : ι → σ) [IsRingFiltration F F_lt]
  {M : Type*} [AddCommGroup M] [Module R M] {σM : Type*} [SetLike σM M] [AddSubgroupClass σM M]
  {N : Type*} [AddCommGroup N] [Module R N] {σN : Type*} [SetLike σN N] [AddSubgroupClass σN N]
  (FM : ι → σM) (FM_lt : ι → σM) (FN : ι → σN) (FM_lt : ι → σM) (FN_lt : ι → σN)
  [filM : IsModuleFiltration F F_lt FM FM_lt] [filN : IsModuleFiltration F F_lt FN FN_lt]

open DirectSum TensorProduct Pointwise

def indices (i : ι) := {x : ι × ι // x.1 + x.2 = i}

noncomputable def FilteredPiece (i : ι) : Submodule ℤ (M ⊗[ℤ] N) := ⨆ x : indices i, LinearMap.range
  (mapIncl (AddSubgroup.toIntSubmodule (AddSubmonoidClass.subtype (FM x.1.1)).range)
  (AddSubgroup.toIntSubmodule (AddSubmonoidClass.subtype (FN x.1.2)).range))

instance tensor_filtration : IsModuleFiltration F F_lt (FilteredPiece FM FN) where
  mono := by
    simp only [FilteredPiece, range_mapIncl]
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
    simp only [vadd_eq_add, FilteredPiece, range_mapIncl, AddSubgroup.coe_toIntSubmodule,
      AddMonoidHom.coe_range, AddSubmonoidClass.coe_subtype, Subtype.range_coe_subtype,
      Submodule.iSup_span, Submodule.smul_span]
    apply Submodule.span_mono
    simp only [← Set.singleton_smul, Set.smul_iUnion, Set.iUnion_subset_iff]
    intro indj
    simp only [Set.singleton_smul]
    apply Set.smul_set_subset_iff.mpr
    rintro y ⟨m, hm, n, hn, heq⟩
    simpa [Set.mem_iUnion, Set.mem_image2, Set.mem_setOf_eq] using ⟨⟨(i + indj.1.1, indj.1.2), by
      rw [add_assoc, indj.2]⟩, ⟨x • m, ⟨filM.2 hx hm, ⟨n, ⟨hn, by simp only [← smul_tmul', heq]⟩⟩⟩⟩⟩
