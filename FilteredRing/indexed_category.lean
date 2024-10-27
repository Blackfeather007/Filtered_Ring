import Mathlib

universe o u v w

open Pointwise CategoryTheory

variable {R : Type u} {ι : Type v} [Ring R] [OrderedAddCommMonoid ι] {σ : Type o} [SetLike σ R]
  (F : ι → σ)

structure IndexedModuleCat where
  Mod : ModuleCat.{w, u} R
  {σMod : Type*}
  [instSetLike : SetLike σMod Mod.carrier]
  [instAddSubmonoidClass : AddSubmonoidClass σMod Mod.carrier]
  fil : ι → σMod
  [f : SetLike.GradedSMul F fil]

instance {M : IndexedModuleCat F} : SetLike M.σMod M.Mod.carrier := M.instSetLike

instance {M : IndexedModuleCat F} : AddSubmonoidClass M.σMod M.Mod.carrier :=
  M.instAddSubmonoidClass

instance {M : IndexedModuleCat F} {i : ι} : AddSubmonoid M.Mod where
  carrier := Set.range (AddSubmonoidClass.subtype (M.fil i))
  add_mem' {a b} ha hb := by
    rw [AddSubmonoidClass.coe_subtype, Subtype.range_coe_subtype, Set.mem_setOf_eq] at *
    exact add_mem ha hb
  zero_mem' := by
    show 0 ∈ Set.range ⇑(AddSubmonoidClass.subtype (M.fil i))
    rw [AddSubmonoidClass.coe_subtype, Subtype.range_coe_subtype, Set.mem_setOf_eq]
    exact zero_mem (M.fil i)

instance IndexedModuleCategory : Category (IndexedModuleCat F) where
  Hom M N := {f : M.Mod →ₗ[R] N.Mod //
    ∀ i, f '' Set.range (AddSubmonoidClass.subtype (M.fil i))
    ≤ Set.range (AddSubmonoidClass.subtype (N.fil i))}
  id _ := ⟨LinearMap.id, fun i ↦ by
    simp only [LinearMap.id_coe, id_eq, Set.image_id', le_refl]⟩
  comp f g := ⟨g.1.comp f.1, fun i ↦ by
    have aux1 := f.2 i
    have aux2 := g.2 i
    simp only [Set.le_eq_subset, Set.image_subset_iff] at *
    exact fun _ hx ↦ aux2 <| aux1 hx⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

instance {M N : IndexedModuleCat F} : FunLike (M ⟶ N) M.1 N.1 where
  coe f := f.1.toFun
  coe_injective' _ _ h := propext Subtype.val_inj |>.symm.mpr <| DFunLike.coe_injective' h

instance IndexedModuleConcreteCategory : ConcreteCategory (IndexedModuleCat F) where
  forget :=
    { obj := fun R ↦ R.Mod
      map := fun f ↦ f.val }
  forget_faithful := ⟨fun {_ _} ⦃_ _⦄ ht ↦ Subtype.val_inj.mp (LinearMap.ext_iff.mpr (congrFun ht))⟩

@[simp] lemma forget_map {M N : IndexedModuleCat F} (f : M ⟶ N) :
  (forget <| IndexedModuleCat F).map f = (f : M.Mod → N.Mod) := rfl
