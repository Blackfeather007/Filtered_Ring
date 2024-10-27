import FilteredRing.Basic
import FilteredRing.indexed_category

universe o u v w

open Pointwise CategoryTheory

variable {R : Type u} {ι : Type v} [Ring R] [OrderedAddCommMonoid ι] {σ : Type o} [SetLike σ R]
  (F : ι → σ)

structure FilteredModuleCat where
  Mod : ModuleCat.{w, u} R
  {σMod : Type*}
  [instSetLike : SetLike σMod Mod.carrier]
  [instAddSubmonoidClass : AddSubmonoidClass σMod Mod.carrier]
  fil : ι → σMod
  [f : FilteredModule F fil]

attribute [instance] FilteredModuleCat.instSetLike FilteredModuleCat.instAddSubmonoidClass
  FilteredModuleCat.f

instance {M : FilteredModuleCat F} : IndexedModuleCat F where
  Mod := M.Mod
  σMod := M.σMod
  instSetLike := M.instSetLike
  instAddSubmonoidClass := M.instAddSubmonoidClass
  fil := M.fil
  f := {smul_mem := fun _ _ _ _ ha hb ↦ M.f.smul_mem ha hb}

namespace FilteredModuleCat

instance {M : FilteredModuleCat F} {i : ι} : AddSubmonoid M.Mod where
  carrier := Set.range (AddSubmonoidClass.subtype (M.fil i))
  add_mem' {a b} ha hb := by
    rw [AddSubmonoidClass.coe_subtype, Subtype.range_coe_subtype, Set.mem_setOf_eq] at *
    exact add_mem ha hb
  zero_mem' := by
    show 0 ∈ Set.range ⇑(AddSubmonoidClass.subtype (M.fil i))
    rw [AddSubmonoidClass.coe_subtype, Subtype.range_coe_subtype, Set.mem_setOf_eq]
    exact zero_mem (M.fil i)

instance filteredModuleCategory : Category (FilteredModuleCat F) where
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

instance {M N : FilteredModuleCat F} : FunLike (M ⟶ N) M.1 N.1 where
  coe f := f.1.toFun
  coe_injective' _ _ h := propext Subtype.val_inj |>.symm.mpr <| DFunLike.coe_injective' h

instance filteredModuleConcreteCategory : ConcreteCategory (FilteredModuleCat F) where
  forget :=
    { obj := fun R ↦ R.Mod
      map := fun f ↦ f.val }
  forget_faithful := ⟨fun {_ _} ⦃_ _⦄ ht ↦ Subtype.val_inj.mp (LinearMap.ext_iff.mpr (congrFun ht))⟩

@[simp] lemma forget_map {M N : FilteredModuleCat F} (f : M ⟶ N) :
  (forget (FilteredModuleCat F)).map f = (f : M.Mod → N.Mod) := rfl

/-- The object in the category of R-filt associated to an filtered R-module -/
def of {X : Type w} [AddCommGroup X] [Module R X] {σX : Type*} [SetLike σX X]
  [AddSubmonoidClass σX X] (filX : ι → σX) [FilteredModule F filX] : FilteredModuleCat F where
    Mod := ModuleCat.of R X
    σMod := σX
    instAddSubmonoidClass := by trivial
    fil := filX

instance {X : FilteredModuleCat F} : FilteredModule F X.fil := X.f

@[simp] theorem of_coe (X : FilteredModuleCat F) : of F X.fil = X := rfl

@[simp] theorem coe_of (X : Type w) [AddCommGroup X] [Module R X] {σX : Type*} [SetLike σX X]
  [AddSubmonoidClass σX X] (filX : ι → σX) [FilteredModule F filX] : (of F filX).1 = X := rfl

/-- A `LinearMap` with degree 0 is a morphism in `Module R`. -/
def ofHom {X Y : Type w} {σX σY : Type o} [AddCommGroup X] [Module R X] [SetLike σX X]
  [AddSubmonoidClass σX X] (filX : ι → σX) [FilteredModule F filX] [AddCommGroup Y] [Module R Y]
  [SetLike σY Y] [AddSubmonoidClass σY Y] (filY : ι → σY) [FilteredModule F filY] (f : X →ₗ[R] Y)
  (deg0 : ∀ i, f '' Set.range (AddSubmonoidClass.subtype (filX i))
    ≤ Set.range (AddSubmonoidClass.subtype (filY i))) :
    of F filX ⟶ of F filY :=
    ⟨f, deg0⟩

-- @[simp 1100] ← 有lint错误
theorem ofHom_apply {X Y : Type w} {σX σY : Type o} [AddCommGroup X] [Module R X] [SetLike σX X]
  [AddSubmonoidClass σX X] (filX : ι → σX) [FilteredModule F filX] [AddCommGroup Y] [Module R Y]
  [SetLike σY Y] [AddSubmonoidClass σY Y] (filY : ι → σY) [FilteredModule F filY] (f : X →ₗ[R] Y)
  (deg0 : ∀ i, f '' Set.range (AddSubmonoidClass.subtype (filX i))
    ≤ Set.range (AddSubmonoidClass.subtype (filY i))) (x : X) :
  ofHom F filX filY f deg0 x = f x := rfl

/-- Forgetting to the underlying type and then building the bundled object returns the original
filtered module. -/
-- Have no idea what ↑ means...
@[simps]
def ofSelfIso (M : FilteredModuleCat F) : of F M.fil ≅ M where
  hom := 𝟙 M
  inv := 𝟙 M

@[simp]
theorem id_apply {M : FilteredModuleCat F} (m : M.1) : (𝟙 M : M.1 → M.1) m = m := rfl

@[simp]
theorem coe_comp {M N U : FilteredModuleCat F} (f : M ⟶ N) (g : N ⟶ U) :
  (f ≫ g : M.1 → U.1) = g ∘ f := rfl

-- instance : Inhabited (FilteredModuleCat F) := {
--   default := {
--     Mod := ModuleCat.of R PUnit
--     σMod := (⊤ : AddSubmonoid (Mod F))

--   }
-- }

private instance {M N : FilteredModuleCat F} : AddSemigroup (M ⟶ N) where
  add f g := ⟨f.1 + g.1, by
    simp only [Set.le_eq_subset, Set.image_subset_iff]
    intro i _ hx
    have aux1 := f.2 i
    have aux2 := g.2 i
    simp only [AddSubmonoidClass.coe_subtype, Subtype.range_coe_subtype, Set.le_eq_subset,
      Set.image_subset_iff, Set.preimage_setOf_eq] at *
    exact add_mem (aux1 hx) (aux2 hx)⟩
  add_assoc a b c := propext Subtype.val_inj |>.symm.mpr
    <| add_assoc a.1 b.1 c.1

private instance {M N : FilteredModuleCat F} : AddCommMonoid (M ⟶ N) where
  zero := ⟨0, fun i ↦ by
    simp only [Set.le_eq_subset]
    repeat rw [AddSubmonoidClass.coe_subtype, Subtype.range_coe_subtype]
    rw [Set.image_subset_iff]
    exact fun a _ ↦ zero_mem (N.fil i)⟩
  zero_add a := propext Subtype.val_inj |>.symm.mpr
    <| AddZeroClass.zero_add a.1
  add_zero a := propext Subtype.val_inj |>.symm.mpr
    <| AddZeroClass.add_zero a.1
  nsmul k f := ⟨k • f.1, by
    simp only [Set.le_eq_subset, Set.image_subset_iff]
    intro i _ hx
    have aux := f.2 i
    simp only [AddSubmonoidClass.coe_subtype, Subtype.range_coe_subtype, Set.mem_setOf_eq,
      Set.le_eq_subset, Set.image_subset_iff, Set.preimage_setOf_eq] at *
    exact nsmul_mem (aux hx) k⟩
  nsmul_zero _ := by
    simp only [Set.le_eq_subset, zero_smul]; rfl
  nsmul_succ n x := propext Subtype.val_inj |>.symm.mpr
    <| succ_nsmul x.1 n
  add_comm f g := propext Subtype.val_inj |>.symm.mpr
    <| AddCommMagma.add_comm f.1 g.1

private instance {M N : FilteredModuleCat F} [AddSubgroupClass N.σMod N.Mod.carrier] :
  SubNegMonoid (M ⟶ N) where
  zsmul k f := ⟨k • f.1, by
    simp only [Set.le_eq_subset, LinearMap.smul_apply, Set.image_subset_iff]
    intro i _ hx
    have aux := f.2 i
    simp only [AddSubmonoidClass.coe_subtype, Subtype.range_coe_subtype, Set.mem_setOf_eq,
      Set.le_eq_subset, Set.image_subset_iff, Set.preimage_setOf_eq] at *
    exact zsmul_mem (aux hx) k⟩
  neg f := ⟨- f.1, by
    simp only [Set.le_eq_subset, LinearMap.neg_apply, Set.image_subset_iff]
    intro i _ hx
    have aux := f.2 i
    simp only [AddSubmonoidClass.coe_subtype, Subtype.range_coe_subtype, Set.mem_setOf_eq,
      Set.le_eq_subset, Set.image_subset_iff, Set.preimage_setOf_eq,
      neg_mem_iff] at *
    exact aux hx⟩
  zsmul_zero' f := by
    simp only [Set.le_eq_subset, zero_smul]; rfl
  zsmul_succ' k f := by
    rw [← Subtype.val_inj]
    simp only [Nat.succ_eq_add_one, Int.ofNat_eq_coe, Nat.cast_one, Set.le_eq_subset, natCast_zsmul]
    exact succ_nsmul f.1 k
  zsmul_neg' k f := by
    rw [← Subtype.val_inj]
    simp only [Set.le_eq_subset, negSucc_zsmul, Nat.cast_add, Nat.cast_one, neg_inj]
    norm_cast

instance {M N : FilteredModuleCat F} [AddSubgroupClass N.σMod N.Mod.carrier] :
  AddCommGroup (M ⟶ N) where
  neg_add_cancel f := propext Subtype.val_inj |>.symm.mpr
    <| neg_add_cancel f.1
  add_comm := AddCommMagma.add_comm

instance (h : ∀ P : FilteredModuleCat F, AddSubgroupClass P.σMod P.Mod.carrier) :
  Preadditive (FilteredModuleCat F) where
  add_comp P Q R f f' g := by
    exact propext Subtype.val_inj |>.symm.mpr <| LinearMap.comp_add f.1 f'.1 g.1

private def F' (m : ModuleCat.{w, u} R) := fun i ↦
  AddSubmonoid.closure {x | ∃ r ∈ F i, ∃ a : m.1, x = r • a}

private def proofGP (m : ModuleCat.{w, u} R) (i j : ι) (x : R) : AddSubmonoid m.1 := {
  carrier := {z | x • z ∈ F' F m (j + i)}
  add_mem' := fun {a b} ha hb ↦ by
    simp only [F', Set.mem_setOf_eq, smul_add]
    exact AddSubmonoid.add_mem (AddSubmonoid.closure {x | ∃ r ∈ F (j + i), ∃ a, x = r • a}) ha hb
  zero_mem' :=
    congrArg (Membership.mem (F' F m (j + i))) (smul_zero x) |>.mpr (F' F m (j + i)).zero_mem }

open AddSubmonoid in
instance toFilteredModule (m : ModuleCat.{w, u} R) [FilteredRing F] :
  FilteredModule F (F' F m) where
  mono := fun hij ↦ by
    simp only [F', closure_le]
    rintro x ⟨r, ⟨hr, ⟨a, ha⟩⟩⟩
    exact mem_closure.mpr fun K hk ↦ hk <| Exists.intro r ⟨FilteredRing.mono hij hr,
      Exists.intro a ha⟩
  smul_mem {j i x y} hx hy := by
    have : F' F m i ≤ proofGP F m i j x := by
      apply closure_le.2
      rintro h ⟨r', hr', ⟨a, ha⟩⟩
      exact ha.symm ▸ mem_closure.mpr fun K hk ↦ hk ⟨x * r', ⟨FilteredRing.mul_mem hx hr',
        ⟨a, smul_smul x r' a⟩⟩⟩
    exact this hy

open AddSubmonoid in
def DeducedFunctor [FilteredRing F] : CategoryTheory.Functor (ModuleCat.{w, u} R)
  (FilteredModuleCat F) where
    obj m := { Mod := m, fil := F' F m, f := toFilteredModule F m }
    map := fun {X Y} hom ↦ ⟨hom, by
      rintro i p ⟨x, ⟨hx1, hx2⟩⟩
      set toAddGP := (closure {x : Y.1 | ∃ r ∈ F i, ∃ a, x = r • a}).comap hom.toAddMonoidHom
      rw [AddSubmonoidClass.coe_subtype, Subtype.range_coe_subtype, Set.mem_setOf_eq] at *
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

/-- ! To-do

instance : Inhabited (ModuleCat R) :=
  ⟨of R PUnit⟩

instance ofUnique {X : Type v} [AddCommGroup X] [Module R X] [i : Unique X] : Unique (of R X) :=
  i -/
example : 1 = 1 := rfl

end FilteredModuleCat
