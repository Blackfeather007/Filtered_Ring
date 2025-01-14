import FilteredRing.Basic

universe o u v w

class SubmoduleClass (R T M : Type*)
  [Semiring R] [AddCommMonoid M] [Module R M] [SetLike T M]
  extends AddSubmonoidClass T M, SMulMemClass T R M

open Pointwise CategoryTheory Subtype

variable {R : Type u} {ι : Type v} [Ring R] [OrderedAddCommMonoid ι] {σ : Type o}
  [SetLike σ R] (F : ι → σ) (F_lt : outParam <| ι → σ) [IsRingFiltration F F_lt]

structure FilteredModuleCat where
  Mod : ModuleCat.{w, u} R
  {σMod : Type*}
  [instSetLike : SetLike σMod Mod.carrier]
  [instAddSubgroupClass : AddSubgroupClass σMod Mod.carrier]
  fil : ι → σMod
  fil_lt : ι → σMod
  [instIsModuleFiltration : IsModuleFiltration F F_lt fil fil_lt]

namespace FilteredModuleCat

attribute [instance] FilteredModuleCat.instSetLike FilteredModuleCat.instAddSubgroupClass FilteredModuleCat.instIsModuleFiltration

instance : Category (FilteredModuleCat F F_lt) where
  Hom M N := {f : M.Mod →ₗ[R] N.Mod // ∀ (i : ι) (x : M.fil i), f x ∈ N.fil i}
  id _ := ⟨LinearMap.id, fun i x ↦ by
    simp only [LinearMap.id_coe, id_eq, SetLike.coe_mem]⟩
  comp f g := ⟨g.1.comp f.1, fun i x ↦ g.2 i ⟨f.1 x, f.2 i x⟩⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

instance {M N : FilteredModuleCat F F_lt} : FunLike (M ⟶ N) M.1 N.1 where
  coe f := f.1.toFun
  coe_injective' _ _ h := val_inj.1 <| DFunLike.coe_injective' h

instance : ConcreteCategory (FilteredModuleCat F F_lt) where
  forget :=
    { obj := fun R ↦ R.Mod
      map := fun f ↦ f.val }
  forget_faithful := ⟨fun {_ _} ⦃_ _⦄ ht ↦ val_inj.mp <| LinearMap.ext_iff.mpr
    <| congrFun ht⟩

private instance {M N : FilteredModuleCat F F_lt} : AddSemigroup (M ⟶ N) where
  add f g := ⟨f.1 + g.1, fun i x ↦ add_mem (f.2 i x) (g.2 i x)⟩
  add_assoc a b c := val_inj.1 <| add_assoc a.1 b.1 c.1

private instance {M N : FilteredModuleCat F F_lt} : AddCommMonoid (M ⟶ N) where
  zero := ⟨0, fun i _ ↦ zero_mem (N.fil i)⟩
  zero_add a := val_inj.1 <| zero_add a.1
  add_zero a := val_inj.1 <| add_zero a.1
  nsmul n a := ⟨n • a.1, fun i x ↦ nsmul_mem (a.2 i x) n⟩
  nsmul_zero f := by simp only [zero_smul]; rfl
  nsmul_succ n a := val_inj.1 <| succ_nsmul a.1 n
  add_comm a b := val_inj.1 <| add_comm a.1 b.1

private instance {M N : FilteredModuleCat F F_lt} [AddSubgroupClass N.σMod N.Mod.carrier] :
    SubNegMonoid (M ⟶ N) where
  neg a := ⟨-a.1, fun i x ↦ neg_mem (a.2 i x)⟩
  sub a b := ⟨a.1 - b.1, fun i x ↦ sub_mem (a.2 i x) (b.2 i x)⟩
  sub_eq_add_neg a b := val_inj.1 <| sub_eq_add_neg a.1 b.1
  zsmul z a := ⟨z • a.1, fun i x ↦ zsmul_mem (a.2 i x) z⟩
  zsmul_zero' a := by simp only [zero_smul]; rfl
  zsmul_succ' n a := by
    simp only [Nat.succ_eq_add_one, Int.ofNat_eq_coe, Nat.cast_add, Nat.cast_one, natCast_zsmul]
    apply val_inj.1
    show (((n : ℤ) + 1) • a.1) = (n • a.1 + a.1)
    rw [add_smul, one_smul, natCast_zsmul]
  zsmul_neg' z a := by
    simp only [negSucc_zsmul, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
    apply val_inj.1
    show -((z + 1) • a.1) = -(((z : ℤ) + 1) • a.1)
    rw [add_smul, add_smul, natCast_zsmul, one_smul, one_smul]

instance {M N : FilteredModuleCat F F_lt} [AddSubgroupClass N.σMod N.Mod.carrier] :
    AddCommGroup (M ⟶ N) where
  neg_add_cancel f := val_inj.1 <| neg_add_cancel f.1
  add_comm := AddCommMagma.add_comm

end FilteredModuleCat

namespace DeducedFunctor

variable (M : ModuleCat.{w, u} R) (σMod : Type*)
  [SetLike σMod M.1] [AddSubgroupClass σMod M.1]
  (F' : ι → σMod) (F'_lt : outParam <| ι → σMod) [IsRingFiltration F F_lt]

class InducedFilteredModule extends IsRingFiltration F F_lt : Prop where
  containsF : ∀ i : ι, {x | ∃ r ∈ F i, ∃ a : M.1, x = r • a} ⊆ F' i
  closureF : ∀ s : σMod, {x | ∃ r ∈ F i, ∃ a : M.1, x = r • a} ⊆ s → F' i ≤ s
  -- containsFlt : ∀ i : ι, {x | ∃ r ∈ F_lt i, ∃ a : M.1, x = r • a} ⊆ F'_lt i
  -- closureFlt : ∀ s : σMod, {x | ∃ r ∈ F_lt i, ∃ a : M.1, x = r • a} ⊆ s → F'_lt i ≤ s

theorem induceFil [InducedFilteredModule F F_lt M σMod F'] : IsFiltration F' F'_lt where
  mono {i j} hij := by
    suffices {x : M.1 | ∃ r ∈ F i, ∃ a : M.1, x = r • a} ⊆ F' j from
      InducedFilteredModule.closureF (F' j) this (F_lt := F_lt) (F' := F')
    suffices {x : M.1 | ∃ r ∈ F i, ∃ a, x = r • a} ⊆ {x | ∃ r ∈ F j, ∃ a, x = r • a} from
      Set.Subset.trans this <|
        InducedFilteredModule.containsF j (F_lt := F_lt) (F' := F') (F := F) (M := M)
    intro x hx
    rw [Set.mem_setOf_eq] at hx ⊢
    obtain ⟨r, ⟨hr1, ⟨a, hr2⟩⟩⟩ := hx
    use r
    constructor
    · exact (IsFiltration.mono hij (F := F) (A := R)) hr1
    · exact ⟨a, hr2⟩
  is_le {j i} hij := by
    suffices {x : M.1 | ∃ r ∈ F i, ∃ a : M.1, x = r • a} ⊆ F'_lt j from
      InducedFilteredModule.closureF (F'_lt j) this (F_lt := F_lt) (F' := F')

  is_sup := sorry

theorem induced (h : InducedFilteredModule F F_lt M σMod F') :
    IsModuleFiltration F F_lt F' F'_lt where
  mono {i j} hij := by
    suffices {x : M.1 | ∃ r ∈ F i, ∃ a : M.1, x = r • a} ⊆ F' j from
      InducedFilteredModule.closureF (F' j) this (F_lt := F_lt) (F' := F')
    suffices {x : M.1 | ∃ r ∈ F i, ∃ a, x = r • a} ⊆ {x | ∃ r ∈ F j, ∃ a, x = r • a} from
      Set.Subset.trans this <|
        InducedFilteredModule.containsF j (F_lt := F_lt) (F' := F') (F := F) (M := M)
    intro x hx
    rw [Set.mem_setOf_eq] at hx ⊢
    obtain ⟨r, ⟨hr1, ⟨a, hr2⟩⟩⟩ := hx
    use r
    constructor
    · exact (IsFiltration.mono hij (F := F) (A := R)) hr1
    · exact ⟨a, hr2⟩
  is_le {j i} hij := by
    suffices {x : M.1 | ∃ r ∈ F i, ∃ a : M.1, x = r • a} ⊆ F'_lt j from
      InducedFilteredModule.closureF (F'_lt j) this (F_lt := F_lt) (F' := F')
    suffices {x : M.1 | ∃ r ∈ F i, ∃ a : M.1, x = r • a} ⊆ {x | ∃ r ∈ F_lt j, ∃ a : M.1, x = r • a} from
      Set.Subset.trans this <|
        InducedFilteredModule.containsFlt j (F'_lt := F'_lt) (F := F) (M := M) (F_lt := F_lt) (F' := F')
    intro x hx
    rw [Set.mem_setOf_eq] at hx ⊢
    obtain ⟨r, ⟨hr1, ⟨a, hr2⟩⟩⟩ := hx
    use r
    constructor
    · exact (IsFiltration.is_le hij (F := F) (A := R)) hr1
    · exact ⟨a, hr2⟩
  is_sup := by
    intro B j hij
    suffices {x : M.1 | ∃ r ∈ F_lt j, ∃ a : M.1, x = r • a} ⊆ B from
      InducedFilteredModule.closureFlt F F' B this
    have : ∀ i < j, F' i ≤ B := by
      intro i hji
      replace hij := hij i hji
      have : {x : M.1 | ∃ r ∈ F i, ∃ a : M.1, x = r • a} ⊆ B := by

  smul_mem := sorry


noncomputable def F' : ι → σMod := fun i ↦ Classical.choose (hclosure i)
noncomputable def F'_lt : ι → σMod := fun i ↦ Classical.choose (hclosure' i)

private def proofGP (i j : ι) (x : R) : AddSubgroup M.1 := {
  carrier := {z | x • z ∈ F' F M σMod hclosure (j + i)}
  add_mem' := fun {a b} ha hb ↦ by
    simp only [F', Set.mem_setOf_eq, smul_add, Set.mem_setOf_eq] at ha hb ⊢
    exact add_mem ha hb
  zero_mem' := by
    simp only [Set.mem_setOf_eq, smul_zero]
    exact zero_mem (F' F M σMod hclosure (j + i))
  neg_mem' := by
    simp only [Set.mem_setOf_eq, smul_neg, neg_mem_iff, imp_self, implies_true]
}

open AddSubmonoid in
def DeducedFunctor [IsRingFiltration F F_lt] : CategoryTheory.Functor (ModuleCat.{w, u} R)
  (FilteredModuleCat F F_lt) where
    obj m := { Mod := m, fil := F' F m, instFilteredModule := toFilteredModule F m }
    map := fun {X Y} hom ↦ ⟨hom, by
      rintro i p ⟨x, ⟨hx1, hx2⟩⟩
      set toAddGP := (closure {x : Y.1 | ∃ r ∈ F i, ∃ a, x = r • a}).comap hom.toAddMonoidHom
      rw [AddSubmonoidClass.coe_, .range_coe_, Set.mem_setOf_eq] at *
      suffices x ∈ toAddGP from hx2.symm ▸ this
      suffices closure {x : X.1 | ∃ r ∈ F i, ∃ a, x = r • a} ≤ toAddGP from this hx1
      suffices {x : X.1 | ∃ r ∈ F i, ∃ a, x = r • a} ⊆ hom ⁻¹' {x : Y.1 | ∃ r ∈ F i, ∃ a, x = r • a}
        from by
          apply closure_le.2
          exact fun ⦃_⦄ t ↦ subset_closure (this t)
      simp only [Set.preimage_setOf_eq, Set.setOf_subset_setOf, forall_exists_index, and_imp]
      exact fun a x hx x' hx' ↦ ⟨x, ⟨hx, (congrArg (fun t ↦ ∃ a, hom t = x • a) hx').mpr
        <| (congrArg (fun t ↦ ∃ a, t = x • a) (map_smul hom x x')).mpr <|
          exists_apply_eq_apply' (HSMul.hSMul x) (hom x')⟩⟩⟩

end DeducedFunctor
