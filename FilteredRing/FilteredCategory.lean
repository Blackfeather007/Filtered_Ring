import FilteredRing.Basic

universe o u v w

namespace Indexed

variable {M γ σ : Type*} (gen : ι → γ) (F' : ι → σ) [Preorder γ] [SetLike σ M] (le : σ →o γ)

class closure : Prop where
  contains : ∀ i : ι, gen i ≤ le.toFun (F' i)
  closure : ∀ s : σ, gen i ≤ le.toFun s → F' i ≤ s

theorem closure_le [closure gen F' le] : F' i ≤ K ↔ gen i ≤ le.toFun K :=
  ⟨fun h ↦ le_trans (closure.contains i) (le.monotone' h), fun h ↦ closure.closure K h⟩

theorem mem_closure [closure gen F' le] : x ∈ F' i ↔ ∀ K, gen i ≤ le.toFun K → x ∈ K :=
  ⟨fun h K hK ↦ (closure.closure K hK) h, fun h ↦ h (F' i) <| closure.contains i⟩

end Indexed

namespace FilteredModule

open CategoryTheory Subtype

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

attribute [instance] FilteredModuleCat.instSetLike FilteredModuleCat.instAddSubgroupClass FilteredModuleCat.instIsModuleFiltration

instance : Category (FilteredModuleCat F F_lt) where
  Hom M N := {f : M.Mod →ₗ[R] N.Mod // ∀ (i : ι) (x : M.fil i), f x ∈ N.fil i}
  id _ := ⟨LinearMap.id, fun i x ↦ by
    simp only [LinearMap.id_coe, id_eq, SetLike.coe_mem]⟩
  comp f g := ⟨g.1.comp f.1, fun i x ↦ g.2 i ⟨f.1 x, f.2 i x⟩⟩

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

end FilteredModule

namespace Induced

variable {R : Type u} {ι : Type v} [Ring R] {σ : Type o}
  [SetLike σ R] (F : ι → σ) (F_lt : outParam <| ι → σ)
variable {M : ModuleCat.{w, u} R} {σMod : Type*} [SetLike σMod M.1] (F' : ι → σMod)

abbrev closure := Indexed.closure (fun i ↦ {x | ∃ r ∈ F i, ∃ a : M.1, x = r • a})
  F' (⟨fun s ↦ s, fun ⦃_ _⦄ a ↦ a⟩ : σMod →o Set M)

theorem closure_le [closure F F'] : F' i ≤ K ↔ {x | ∃ r ∈ F i, ∃ a : M.1, x = r • a} ⊆ K :=
  Indexed.closure_le (fun i ↦ {x | ∃ r ∈ F i, ∃ a : M.1, x = r • a}) F'
    (⟨fun s ↦ s, fun ⦃_ _⦄ a ↦ a⟩ : σMod →o Set M)

theorem mem_closure [closure F F'] : x ∈ F' i ↔
    ∀ (K : σMod), {x | ∃ r ∈ F i, ∃ a : M.1, x = r • a} ⊆ (K : Set M) → x ∈ K :=
  Indexed.mem_closure (fun i ↦ {x | ∃ r ∈ F i, ∃ a : M.1, x = r • a}) F'
    (⟨fun s ↦ s, fun ⦃_ _⦄ a ↦ a⟩ : σMod →o Set M)

end Induced

namespace AddSubgroup

variable {R : Type u} {ι : Type v} [Ring R] [OrderedAddCommMonoid ι] {σ : Type o}
  [SetLike σ R] (F : ι → σ) (F_lt : outParam <| ι → σ) [IsRingFiltration F F_lt]
  {M : ModuleCat.{w, u} R}

variable (F' : ι → AddSubgroup M.1) (F'_lt : outParam <| ι → AddSubgroup M.1)
  [Induced.closure F F'] [IsFiltration F' F'_lt]

private def preimage_group (i j : ι) (x : R) : AddSubgroup M := {
  carrier := {z | x • z ∈ F' (j + i)}
  add_mem' := fun {a b} ha hb ↦ by
    simp only [Set.mem_setOf_eq, smul_add] at ha hb ⊢
    exact (AddSubgroup.add_mem_cancel_right (F' (j + i)) hb).2 ha
  zero_mem' := by
    simp only [Set.mem_setOf_eq, smul_zero]
    exact zero_mem (F' (j + i))
  neg_mem' := by
    simp only [Set.mem_setOf_eq, smul_neg, neg_mem_iff, imp_self, implies_true]
}

instance ModuleFiltration : IsModuleFiltration F F_lt F' F'_lt where
  smul_mem {i j x y} hx hy := by
    have : F' j ≤ preimage_group F' j i x := by
      apply (Induced.closure_le F F').2
      intro h ⟨r', hr', ⟨a, ha⟩⟩
      apply (Induced.mem_closure F F').2
      intro K hK
      rw [ha, smul_smul]
      have mul_mem := IsRingFiltration.mul_mem hx hr'
      set result := (x * r') • a
      have : result ∈ {x | ∃ r ∈ F (i + j), ∃ a, x = r • a} := by
        rw [Set.mem_setOf_eq]
        exact ⟨(x * r'), ⟨mul_mem, ⟨a, rfl⟩⟩⟩
      exact hK this
    have : (F' j).carrier ⊆ {z | x • z ∈ F' (i + j)} := this
    have : y ∈ {z | x • z ∈ F' (i + j)} := this hy
    rwa [Set.mem_setOf_eq] at this

end AddSubgroup

namespace Submodule

variable {R : Type u} [CommRing R] {σ : Type o} [SetLike σ R] (F : ι → σ)
  (F_lt : outParam <| ι → σ) [OrderedAddCommMonoid ι]
  [IsRingFiltration F F_lt] {M : ModuleCat.{w, u} R} (F' : ι → Submodule R M.1)
  (F'_lt : outParam <| ι → Submodule R M.1)

variable [Induced.closure F F'] [IsFiltration F' F'_lt]

private def preimage_module (i j : ι) (x : R) : Submodule R M := {
  carrier := {z | x • z ∈ F' (j + i)}
  add_mem' := fun {a b} ha hb ↦ by
    simpa only [Set.mem_setOf_eq, smul_add] using (Submodule.add_mem_iff_right (F' (j + i)) ha).2 hb
  zero_mem' := by simpa only [Set.mem_setOf_eq, smul_zero] using zero_mem (F' (j + i))
  smul_mem' := fun r m hm ↦ by
    rw [Set.mem_setOf_eq, ← smul_assoc, smul_eq_mul, mul_comm, mul_smul]
    exact (Submodule.smul_mem (F' (j + i)) r hm)
}

instance ModuleFiltration : IsModuleFiltration F F_lt F' F'_lt where
  smul_mem {i j x y} hx hy := by
    have : F' j ≤ preimage_module F' j i x := by
      apply (Induced.closure_le F F').2
      intro h ⟨r', hr', ⟨a, ha⟩⟩
      apply (Induced.mem_closure F F').2
      intro K hK
      rw [ha, smul_smul]
      have : (x * r') • a ∈ {x | ∃ r ∈ F (i + j), ∃ a, x = r • a} := by
        rw [Set.mem_setOf_eq]
        exact ⟨(x * r'), ⟨IsRingFiltration.mul_mem hx hr', ⟨a, rfl⟩⟩⟩
      exact hK this
    have : y ∈ {z | x • z ∈ F' (i + j)} := this hy
    rwa [Set.mem_setOf_eq] at this

end Submodule

namespace DeducedFunctor

variable {R : Type u} {ι : Type v} [Ring R] [OrderedAddCommMonoid ι] {σ : Type o}
  [SetLike σ R] (F : ι → σ) (F_lt : outParam <| ι → σ) [IsRingFiltration F F_lt]

def F' {M : ModuleCat R} :=
  fun i ↦ AddSubgroup.closure {x | ∃ r ∈ F i, ∃ a : M.1, x = r • a}

def F'_lt {M : ModuleCat R} :=
  fun i ↦ AddSubgroup.closure {x | ∃ r ∈ F_lt i, ∃ a : M.1, x = r • a}

-- instance {M : ModuleCat R} : IsFiltration (F' F) (F'_lt F_lt) (σ := (AddSubgroup M.1)) :=
--     sorry

-- instance {M : ModuleCat R} : Induced.IsInducedFiltration F M (F' F) (F'_lt F_lt) where
--   containsF := sorry
--   closureF := sorry

-- def DeducedFunctor : CategoryTheory.Functor (ModuleCat.{w, u} R)
--   (FilteredModuleCat F F_lt) where
--     obj M := {
--       Mod := M
--       σMod := AddSubgroup M
--       fil := F' F
--       fil_lt := F'_lt F_lt
--     }
--     map := fun {X Y} hom ↦ ⟨hom, by
--       rintro i p
--       simp at p ⊢
--       set toAddGP := (AddSubgroup.closure {x : Y.1 | ∃ r ∈ F i, ∃ a, x = r • a}).comap hom.toAddMonoidHom
--       -- rw [AddSubgroupClass.coe_, .range_coe_, Set.mem_setOf_eq] at *
--       suffices x ∈ toAddGP from hx2.symm ▸ this
--       suffices closure {x : X.1 | ∃ r ∈ F i, ∃ a, x = r • a} ≤ toAddGP from this hx1
--       suffices {x : X.1 | ∃ r ∈ F i, ∃ a, x = r • a} ⊆ hom ⁻¹' {x : Y.1 | ∃ r ∈ F i, ∃ a, x = r • a}
--         from by
--           apply closure_le.2
--           exact fun ⦃_⦄ t ↦ subset_closure (this t)
--       simp only [Set.preimage_setOf_eq, Set.setOf_subset_setOf, forall_exists_index, and_imp]
--       exact fun a x hx x' hx' ↦ ⟨x, ⟨hx, (congrArg (fun t ↦ ∃ a, hom t = x • a) hx').mpr
--         <| (congrArg (fun t ↦ ∃ a, t = x • a) (map_smul hom x x')).mpr <|
--           exists_apply_eq_apply' (HSMul.hSMul x) (hom x')⟩⟩⟩

end DeducedFunctor
