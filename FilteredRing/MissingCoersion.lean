import FilteredRing.Basic

@[to_additive]
instance (priority := 50) SubmonoidClass.toSubmonoid {A M : Type*} [Monoid M] [SetLike A M]
    [SubmonoidClass A M] : CoeOut A (Submonoid M) :=
  ⟨fun S ↦ ⟨⟨S, MulMemClass.mul_mem⟩, OneMemClass.one_mem S⟩⟩

@[to_additive]
instance (priority := 50) SubgroupClass.toSubgroup {A M : Type*} [Group M] [SetLike A M]
    [SubgroupClass A M] : CoeOut A (Subgroup M) :=
  ⟨fun S ↦ ⟨⟨⟨S, MulMemClass.mul_mem⟩, OneMemClass.one_mem S⟩, InvMemClass.inv_mem⟩⟩
