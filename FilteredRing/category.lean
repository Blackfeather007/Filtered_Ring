import FilteredRing.Basic

universe u v w

open Pointwise CategoryTheory

variable {R : Type u} {ι : Type v} [Ring R] [OrderedAddCommMonoid ι]
variable (F : ι → AddSubgroup R)

structure FilModCat where
  Mod : ModuleCat.{w, u} R
  fil : ι → AddSubgroup Mod.carrier
  [f : FilteredModule F fil]

instance : Category (FilModCat F) where
  Hom M N := {f : M.Mod →ₗ[R] N.Mod // ∀ i, f '' M.fil i ≤ N.fil i}
  id _ := ⟨LinearMap.id, fun i ↦ by simp only [LinearMap.id_coe, id_eq, Set.image_id', le_refl]⟩
  comp f g := ⟨g.1.comp f.1, fun i ↦ by
    have aux1 := f.2 i
    have aux2 := g.2 i
    simp_all only [Set.le_eq_subset, Set.image_subset_iff, LinearMap.coe_comp, Function.comp_apply]
    exact fun _ hx ↦ aux2 <| aux1 hx⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

instance {M N : FilModCat F} : FunLike (M ⟶ N) M.1 N.1 where
  coe f := f.1.toFun
  coe_injective' _ _ h := propext Subtype.val_inj |>.symm.mpr <| DFunLike.coe_injective' h

/-- The object in the category of R-filt associated to an filtered R-module -/
def of (X : Type w) [AddCommGroup X] [Module R X] (filX : ι → AddSubgroup X)
  [FilteredModule F filX] : FilModCat F where
    Mod := ModuleCat.of R X
    fil := by
      simp only [ModuleCat.coe_of]
      use filX
    f := by simpa [ModuleCat.coe_of]

@[simp] theorem of_coe (X : FilModCat F) : @of R _ _ _ F X.1 _ _ X.2 X.3 = X := rfl

@[simp] theorem coe_of (X : Type w) [AddCommGroup X] [Module R X] (filX : ι → AddSubgroup X)
  [FilteredModule F filX] : (of F X filX).1 = X := rfl

/-- A `LinearMap` with degree 0 is a morphism in `Module R`. -/
def ofHom {X Y : Type w} [AddCommGroup X] [Module R X] {filX : ι → AddSubgroup X}
  [FilteredModule F filX] [AddCommGroup Y] [Module R Y] {filY : ι → AddSubgroup Y}
  [FilteredModule F filY] (f : X →ₗ[R] Y) (deg0 : ∀ i, f '' filX i ≤ filY i) :
  of F X filX ⟶ of F Y filY :=
    ⟨f, deg0⟩

@[simp 1100]
theorem ofHom_apply {X Y : Type w} [AddCommGroup X] [Module R X] {filX : ι → AddSubgroup X}
  [FilteredModule F filX] [AddCommGroup Y] [Module R Y] {filY : ι → AddSubgroup Y}
  [FilteredModule F filY] (f : X →ₗ[R] Y) (deg0 : ∀ i, f '' filX i ≤ filY i) (x : X) :
  ofHom F f deg0 x = f x := rfl

/-- Forgetting to the underlying type and then building the bundled object returns the original
filtered module. -/
-- Have no idea what ↑ means...
@[simps]
def ofSelfIso (M : FilModCat F) : @of R _ _ _ F M.1 _ _ M.2 M.3 ≅ M where
  hom := 𝟙 M
  inv := 𝟙 M

@[simp]
theorem id_apply {M : FilModCat F} (m : M.1) : (𝟙 M : M.1 → M.1) m = m := rfl

@[simp]
theorem coe_comp {M N U : FilModCat F} (f : M ⟶ N) (g : N ⟶ U) : (f ≫ g : M.1 → U.1) = g ∘ f :=
  rfl

/-- ! To-do

instance moduleConcreteCategory : ConcreteCategory.{v} (ModuleCat.{v} R) where
  forget :=
    { obj := fun R => R
      map := fun f => f.toFun }
  forget_faithful := ⟨fun h => LinearMap.ext (fun x => by
    dsimp at h
    rw [h])⟩

instance : Inhabited (ModuleCat R) :=
  ⟨of R PUnit⟩

instance ofUnique {X : Type v} [AddCommGroup X] [Module R X] [i : Unique X] : Unique (of R X) :=
  i

@[simp] lemma forget_map (f : M ⟶ N) : (forget (ModuleCat R)).map f = (f : M → N) := rfl
-/

instance FilModCat.HomAddSemigroup {M N : FilModCat F} : AddSemigroup (M ⟶ N) where
  add f g := ⟨f.1 + g.1, by
    simp only [Set.le_eq_subset, LinearMap.add_apply, Set.image_subset_iff]
    intro i _ hx
    have aux1 := f.2 i
    have aux2 := g.2 i
    simp_all only [SetLike.mem_coe, Set.le_eq_subset, Set.image_subset_iff, Set.mem_preimage]
    exact AddMemClass.add_mem (aux1 hx) (aux2 hx)⟩
  add_assoc a b c := propext Subtype.val_inj |>.symm.mpr
    <| add_assoc a.1 b.1 c.1

instance FilModCat.HomAddMonoid {M N : FilModCat F} : AddMonoid (M ⟶ N) where
  zero := ⟨0, fun i ↦ by simp [AddSubgroup.zero_mem (N.fil i)]⟩
  zero_add a := propext Subtype.val_inj |>.symm.mpr
    <| AddZeroClass.zero_add a.1
  add_zero a := propext Subtype.val_inj |>.symm.mpr
    <| AddZeroClass.add_zero a.1
  nsmul k f := ⟨k • f.1, by
    simp only [Set.le_eq_subset, LinearMap.smul_apply, Set.image_subset_iff]
    intro i a hx
    have aux := f.2 i
    simp_all only [SetLike.mem_coe, Set.le_eq_subset, Set.image_subset_iff, Set.mem_preimage]
    exact AddSubgroup.nsmul_mem (N.fil i) (aux hx) k⟩
  nsmul_zero _ := by
    simp only [Set.le_eq_subset, zero_smul]; rfl
  nsmul_succ n x := propext Subtype.val_inj |>.symm.mpr
    <| succ_nsmul x.1 n

instance FilModCat.HomSubNegMonoid {M N : FilModCat F} : SubNegMonoid (M ⟶ N) where
  zsmul k f := ⟨k • f.1, by
    simp only [Set.le_eq_subset, LinearMap.smul_apply, Set.image_subset_iff]
    intro i _ hx
    have aux := f.2 i
    simp_all only [SetLike.mem_coe, Set.le_eq_subset, Set.image_subset_iff, Set.mem_preimage]
    exact AddSubgroup.zsmul_mem (N.fil i) (aux hx) k⟩
  neg f := ⟨- f.1, by
    simp only [Set.le_eq_subset, LinearMap.neg_apply, Set.image_subset_iff]
    intro i _ hx
    have aux := f.2 i
    simp_all only [SetLike.mem_coe, Set.le_eq_subset, Set.image_subset_iff, Set.mem_preimage,
      neg_mem_iff]
    exact aux hx⟩
  zsmul_zero' f := by
    simp only [Set.le_eq_subset, zero_smul]; rfl
  zsmul_succ' k f := by
    rw [← Subtype.val_inj]
    simp only [Nat.succ_eq_add_one, Int.ofNat_eq_coe, Nat.cast_add, Nat.cast_one, Set.le_eq_subset,
      natCast_zsmul]
    norm_cast
    exact succ_nsmul f.1 k
  zsmul_neg' k f := by
    rw [← Subtype.val_inj]
    simp only [Set.le_eq_subset, negSucc_zsmul, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one,
      neg_inj]
    norm_cast

instance FilModCat.HomAddCommGroup {M N : FilModCat F} : AddCommGroup (M ⟶ N) where
  neg_add_cancel f := propext Subtype.val_inj |>.symm.mpr
    <| neg_add_cancel f.1
  add_comm f g := propext Subtype.val_inj |>.symm.mpr
    <| AddCommMagma.add_comm f.1 g.1

instance : Preadditive (FilModCat F) where
  add_comp P Q R f f' g := by
    exact propext Subtype.val_inj |>.symm.mpr <| LinearMap.comp_add f.1 f'.1 g.1

-- instance [Category (FilModCat R F)] : FilteredRing F := by

--   sorry

-- -- instance (m : ModuleCat.{w, u} R) : FilteredModule F m (fun i ↦ (F i : Set R) • (⊤ : Submodule R m.1)) where
-- --   mono := by
-- --     intro j i hij
-- --     intro x hx

-- instance toFilRing (_ : FilModCat R F) : FilteredRing F :=
--   instFilteredRingOfCategoryFilModCat.{u, v, u, u} R F

def toFun (m : (ModuleCat.{w, u} R)) := fun i ↦ {k : m.1 // ∃ k₁ : F i, ∃ k₂ : m.1, k = (k₁ : R) • k₂}

instance (m : (ModuleCat.{w, u} R)) [hfilR : FilteredRing F] :
  FilteredModule F m fun i ↦ (F i : Set R) • (⊤ : Submodule R m.1) where
  mono := fun i hij ↦ Submodule.set_smul_mono_left ⊤ <| hfilR.mono i hij
  smul_mem := by
    intro j i x y hx hy
    -- (F (i + j) : Set R) • (⊤ : Submodule R m.1)
    let S : Submodule R m.1 := {
      carrier := {z | x • z ∈ (F (i + j) : Set R) • (⊤ : Submodule R m.1)}
      add_mem' := fun hu hv ↦ by simp only [Set.mem_setOf_eq, smul_add, add_mem hu.out hv.out]
      zero_mem' := by simp only [Set.mem_setOf_eq, smul_zero, Submodule.zero_mem]
      smul_mem' := by
        intro r z hz
        simp
        sorry
    }
    sorry


/-
include F in
instance (hcat : FilModCat R F) : CategoryTheory.Functor (ModuleCat.{w, u} R) (FilModCat R F) where
  obj m := {
    Mod := m
    fil := fun i ↦ (F i : Set R) • (⊤ : Submodule R m.1)
    }
    -/
