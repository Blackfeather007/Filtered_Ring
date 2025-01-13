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
  (hclosure : ∀ i : ι, ∃ sub : σMod, Set.range (AddSubgroupClass.subtype sub) =
    AddSubgroup.closure {x | ∃ r ∈ F i, ∃ a : M.1, x = r • a})
  (hclosure' : ∀ i : ι, ∃ sub : σMod, Set.range (AddSubgroupClass.subtype sub) =
    AddSubgroup.closure {x | ∃ r ∈ F_lt i, ∃ a : M.1, x = r • a})

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

open AddSubgroup in
theorem toFilteredModule [IsRingFiltration F F_lt] :
  IsModuleFiltration F F_lt (F' F M σMod hclosure) (F'_lt F_lt M σMod hclosure') where
    mono := fun {i j} hij ↦ by
      simp only [F', closure_le]
      rintro x hx
      set sub1 := Classical.choose (hclosure i) with def_sub1
      set sub2 := Classical.choose (hclosure j) with def_sub2
      have h1 := Classical.choose_spec (hclosure i)
      have h2 := Classical.choose_spec (hclosure j)
      rw [← def_sub1] at h1
      rw [← def_sub2] at h2
      simp only [AddSubgroupClass.coeSubtype, range_coe_subtype] at h1 h2
      replace h1 := Eq.subset h1 hx
      have := IsFiltration.mono hij (F := F) (F_lt := F_lt) (A := R)
      have gen_sub : {x : M.1 | ∃ r ∈ F i, ∃ a, x = r • a} ⊆ {x : M.1 | ∃ r ∈ F j, ∃ a, x = r • a} := by
        simp only [Set.setOf_subset_setOf, forall_exists_index, and_imp]
        exact fun x r hr a hra ↦ ⟨r, ⟨this hr, ⟨a, hra⟩⟩⟩
      have gen_le := closure_mono gen_sub
      replace this : (AddSubgroup.closure {x : M.1 | ∃ r ∈ F i, ∃ a, x = r • a}).carrier ⊆ {x | x ∈ sub2} := by
        rw [h2]; exact gen_le
      exact this h1
    is_le := fun {j i} hij ↦ by
      unfold F' F'_lt
      intro x hx
      set sub2 := Classical.choose (hclosure' j) with def_sub2
      have h1 := Classical.choose_spec (hclosure' i)
      have h2 := Classical.choose_spec (hclosure' j)
      rw [← def_sub2] at h2
      set sub0 := Classical.choose (hclosure i) with def_sub0
      have h0 := Classical.choose_spec (hclosure i)
      rw [← def_sub0] at h0
      simp only [AddSubgroupClass.coeSubtype, range_coe_subtype] at h1 h2 h0
      replace h0 := Eq.subset h0 hx
      have := IsFiltration.is_le hij (F := F) (F_lt := F_lt) (A := R)
      have gen_sub : {x : M.1 | ∃ r ∈ F i, ∃ a, x = r • a} ⊆ {x : M.1 | ∃ r ∈ F_lt j, ∃ a, x = r • a} := by
        simp only [Set.setOf_subset_setOf, forall_exists_index, and_imp]
        exact fun x r hr a hra ↦ ⟨r, ⟨this hr, ⟨a, hra⟩⟩⟩
      have gen_le := closure_mono gen_sub
      replace this : (AddSubgroup.closure {x : M.1 | ∃ r ∈ F i, ∃ a, x = r • a}).carrier ⊆ {x | x ∈ sub2} := by
        rw [h2]; exact gen_le
      exact this h0
    is_sup := fun B j hij ↦ by
      intro x hx
      unfold F' at hij
      unfold F'_lt at hx
      set sub1 := Classical.choose (hclosure' j) with def_sub1
      have h1 := Classical.choose_spec (hclosure' j)
      rw [← def_sub1] at h1
      simp only [AddSubgroupClass.coeSubtype, range_coe_subtype] at h1
      replace h1 := Eq.subset h1 hx
      have base := IsFiltration.is_sup (F := F) (F_lt := F_lt) (A := R) (F j) j
        fun i hij ↦ IsFiltration.mono (F := F) (F_lt := F_lt) (A := R) (le_of_lt hij)
      have gen_sub : {x : M.1 | ∃ r ∈ F_lt j, ∃ a, x = r • a} ⊆ {x : M.1 | ∃ r ∈ F j, ∃ a, x = r • a} := by
        simp only [Set.setOf_subset_setOf, forall_exists_index, and_imp]
        exact fun x r hr a hra ↦ ⟨r, ⟨base hr, ⟨a, hra⟩⟩⟩
      have gen_le := closure_mono gen_sub
      have : (AddSubgroup.closure {x : M.1 | ∃ r ∈ F_lt j, ∃ a, x = r • a}).carrier ⊆ (AddSubgroup.closure {x | ∃ r ∈ F j, ∃ a, x = r • a}).carrier := gen_le
      replace this := this h1

    smul_mem := sorry
  -- mono := fun hij ↦ by
  --   simp only [F', closure_le]
  --   rintro x ⟨r, ⟨hr, ⟨a, ha⟩⟩⟩
  --   exact mem_closure.mpr fun K hk ↦ hk <| Exists.intro r ⟨FilteredRing.mono hij hr,
  --     Exists.intro a ha⟩
  -- smul_mem {j i x y} hx hy := by
  --   have : F' F m i ≤ proofGP F m i j x := by
  --     apply closure_le.2
  --     rintro h ⟨r', hr', ⟨a, ha⟩⟩
  --     exact ha.symm ▸ mem_closure.mpr fun K hk ↦ hk ⟨x * r', ⟨FilteredRing.mul_mem hx hr',
  --       ⟨a, smul_smul x r' a⟩⟩⟩
  --   exact this hy

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
