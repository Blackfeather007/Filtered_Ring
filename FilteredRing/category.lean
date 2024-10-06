import FilteredRing.Basic

universe u v w

open Pointwise CategoryTheory

variable (R : Type u) {ι : Type v} [Ring R] [OrderedAddCommMonoid ι]
variable (F : ι → AddSubgroup R)

structure FilModCat where
  Mod : ModuleCat.{w, u} R
  fil : ι → Submodule R Mod.carrier
  [f : FilteredModule F Mod.carrier fil]

instance : Category (FilModCat R F) where
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

instance {M N : FilModCat R F} : FunLike (M ⟶ N) M.1 N.1 where
  coe f := f.1.toFun
  coe_injective' _ _ h := propext Subtype.val_inj |>.symm.mpr <| DFunLike.coe_injective' h

/-- ! To-do

instance moduleConcreteCategory : ConcreteCategory.{v} (ModuleCat.{v} R) where
  forget :=
    { obj := fun R => R
      map := fun f => f.toFun }
  forget_faithful := ⟨fun h => LinearMap.ext (fun x => by
    dsimp at h
    rw [h])⟩


/-- The object in the category of R-modules associated to an R-module -/
def of (X : Type v) [AddCommGroup X] [Module R X] : ModuleCat R :=
  ⟨X⟩


/-- Typecheck a `LinearMap` as a morphism in `Module R`. -/
def ofHom {R : Type u} [Ring R] {X Y : Type v} [AddCommGroup X] [Module R X] [AddCommGroup Y]
    [Module R Y] (f : X →ₗ[R] Y) : of R X ⟶ of R Y :=
  f

@[simp 1100]
theorem ofHom_apply {R : Type u} [Ring R] {X Y : Type v} [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] (f : X →ₗ[R] Y) (x : X) : ofHom f x = f x :=
  rfl

instance : Inhabited (ModuleCat R) :=
  ⟨of R PUnit⟩

instance ofUnique {X : Type v} [AddCommGroup X] [Module R X] [i : Unique X] : Unique (of R X) :=
  i

@[simp] theorem of_coe (X : ModuleCat R) : of R X = X := rfl

-- Porting note: the simpNF linter complains, but we really need this?!
-- @[simp, nolint simpNF]
theorem coe_of (X : Type v) [AddCommGroup X] [Module R X] : (of R X : Type v) = X :=
  rfl

variable {R}

/-- Forgetting to the underlying type and then building the bundled object returns the original
module. -/
@[simps]
def ofSelfIso (M : ModuleCat R) : ModuleCat.of R M ≅ M where
  hom := 𝟙 M
  inv := 𝟙 M


@[simp]
theorem id_apply (m : M) : (𝟙 M : M → M) m = m :=
  rfl

@[simp]
theorem coe_comp (f : M ⟶ N) (g : N ⟶ U) : (f ≫ g : M → U) = g ∘ f :=
  rfl

theorem comp_def (f : M ⟶ N) (g : N ⟶ U) : f ≫ g = g.comp f :=
  rfl

@[simp] lemma forget_map (f : M ⟶ N) : (forget (ModuleCat R)).map f = (f : M → N) := rfl
-/

instance FilModCat.HomAddSemigroup {M N : FilModCat R F} : AddSemigroup (M ⟶ N) where
  add f g := ⟨f.1 + g.1, by
    simp only [Set.le_eq_subset, LinearMap.add_apply, Set.image_subset_iff]
    intro i _ hx
    have aux1 := f.2 i
    have aux2 := g.2 i
    simp_all only [SetLike.mem_coe, Set.le_eq_subset, Set.image_subset_iff, Set.mem_preimage]
    exact AddMemClass.add_mem (aux1 hx) (aux2 hx)⟩
  add_assoc a b c := propext Subtype.val_inj |>.symm.mpr
    <| add_assoc a.1 b.1 c.1

instance FilModCat.HomAddMonoid {M N : FilModCat R F} : AddMonoid (M ⟶ N) where
  zero := ⟨0, fun i ↦ by simp⟩
  zero_add a := propext Subtype.val_inj |>.symm.mpr
    <| AddZeroClass.zero_add a.1
  add_zero a := propext Subtype.val_inj |>.symm.mpr
    <| AddZeroClass.add_zero a.1
  nsmul k f := ⟨k • f.1, by
    simp only [Set.le_eq_subset, LinearMap.smul_apply, Set.image_subset_iff]
    intro i _ hx
    have aux := f.2 i
    simp_all only [SetLike.mem_coe, Set.le_eq_subset, Set.image_subset_iff, Set.mem_preimage]
    exact Submodule.smul_of_tower_mem (N.fil i) k (aux hx)⟩
  nsmul_zero _ := by
    simp only [Set.le_eq_subset, zero_smul]; rfl
  nsmul_succ n x := propext Subtype.val_inj |>.symm.mpr
    <| succ_nsmul x.1 n

instance FilModCat.HomSubNegMonoid {M N : FilModCat R F} : SubNegMonoid (M ⟶ N) where
  zsmul k f := ⟨k • f.1, by
    simp only [Set.le_eq_subset, LinearMap.smul_apply, Set.image_subset_iff]
    intro i _ hx
    have aux := f.2 i
    simp_all only [SetLike.mem_coe, Set.le_eq_subset, Set.image_subset_iff, Set.mem_preimage]
    exact Submodule.smul_of_tower_mem (N.fil i) k (aux hx)⟩
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

instance FilModCat.HomAddCommGroup {M N : FilModCat R F} : AddCommGroup (M ⟶ N) where
  neg_add_cancel f := propext Subtype.val_inj |>.symm.mpr
    <| neg_add_cancel f.1
  add_comm f g := propext Subtype.val_inj |>.symm.mpr
    <| AddCommMagma.add_comm f.1 g.1

instance : Preadditive (FilModCat R F) where
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
