import FilteredRing.Basic

universe o u v w

open Pointwise CategoryTheory

variable {R : Type u} {ι : Type v} [Ring R] [OrderedAddCommMonoid ι] {σ : Type o} [SetLike σ R]
(F : ι → σ) (F_lt : outParam <| ι → σ) [IsRingFiltration F F_lt]

class FilteredModuleCat where
  Mod : ModuleCat.{w, u} R
  {σMod : Type*}
  [instSetLike : SetLike σMod Mod.carrier]
  [instAddSubmonoidClass : AddSubmonoidClass σMod Mod.carrier]
  fil : ι → σMod
  fil_lt : ι → σMod
  [instIsModuleFiltration : IsModuleFiltration F F_lt fil fil_lt]


namespace FilteredModuleCat

attribute [instance] FilteredModuleCat.instSetLike FilteredModuleCat.instAddSubmonoidClass FilteredModuleCat.instIsModuleFiltration

instance {M : FilteredModuleCat F F_lt} (i : ι) : AddSubmonoid M.Mod where
  carrier := Set.range (AddSubmonoidClass.subtype (M.fil i))
  add_mem' {a b} ha hb := by
    rw [AddSubmonoidClass.coe_subtype, Subtype.range_coe_subtype, Set.mem_setOf_eq] at *
    exact add_mem ha hb
  zero_mem' := by
    simp only [AddSubmonoidClass.coe_subtype, Subtype.range_coe_subtype, Set.mem_setOf_eq, zero_mem (M.fil i)]


instance filteredModuleCategory : Category (FilteredModuleCat F F_lt) where
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


instance {M N : FilteredModuleCat F F_lt} : FunLike (M ⟶ N) M.1 N.1 where
  coe f := f.1.toFun
  coe_injective' _ _ h := propext Subtype.val_inj |>.symm.mpr <| DFunLike.coe_injective' h

instance filteredModuleConcreteCategory : ConcreteCategory (FilteredModuleCat F F_lt) where
  forget :=
    { obj := fun R ↦ R.Mod
      map := fun f ↦ f.val }
  forget_faithful := ⟨fun {_ _} ⦃_ _⦄ ht ↦ Subtype.val_inj.mp (LinearMap.ext_iff.mpr (congrFun ht))⟩


@[simp] lemma forget_map {M N : FilteredModuleCat F F_lt} (f : M ⟶ N) :
  (forget (FilteredModuleCat F F_lt)).map f = (f : M.Mod → N.Mod) := rfl

/-- The object in the category of R-filt associated to an filtered R-module -/
def of {X : Type w} [AddCommGroup X] [Module R X] {σX : Type*} [SetLike σX X]
  [AddSubmonoidClass σX X] (filX : ι → σX) [IsModuleFiltration F filX] : FilteredModuleCat F where
    Mod := ModuleCat.of R X
    σMod := σX
    instAddSubmonoidClass := by trivial
    ind := filX

instance {X : FilteredModuleCat F} : FilteredModule F X.ind := X.instFilteredModule

@[simp] theorem of_coe (X : FilteredModuleCat F) : of F X.ind = X := rfl

@[simp] theorem coe_of (X : Type w) [AddCommGroup X] [Module R X] {σX : Type*} [SetLike σX X]
  [AddSubmonoidClass σX X] (filX : ι → σX) [FilteredModule F filX] : (of F filX).Mod = X := rfl

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
def ofSelfIso (M : FilteredModuleCat F) : of F M.ind ≅ M where
  hom := 𝟙 M
  inv := 𝟙 M

@[simp]
theorem id_apply {M : FilteredModuleCat F} (m : M.Mod) : (𝟙 M : M.Mod → M.Mod) m = m := rfl

@[simp]
theorem coe_comp {M N U : FilteredModuleCat F} (f : M ⟶ N) (g : N ⟶ U) :
  (f ≫ g : M.Mod → U.Mod) = g ∘ f := rfl

-- instance : Inhabited (FilteredModuleCat F) := {
--   default := {
--     Mod := ModuleCat.of R PUnit
--     σMod := (⊤ : AddSubmonoid (Mod F))

--   }
-- }

instance {M N : FilteredModuleCat F} [AddSubgroupClass N.σMod N.Mod.carrier] :
  AddCommGroup (M ⟶ N) := AddCommGroupMorphisms R ι

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
instance toFilteredModule (m : ModuleCat.{w, u} R) [FilteredRing F]: FilteredModule F (F' F m) where
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
    obj m := { Mod := m, ind := F' F m, instFilteredModule := toFilteredModule F m }
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
