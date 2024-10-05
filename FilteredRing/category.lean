import FilteredRing.Basic
open Pointwise CategoryTheory

variable (R : Type u) {ι : Type v} [Ring R] [OrderedAddCommMonoid ι] [DecidableEq ι]
variable (F : ι → AddSubgroup R)
-- instance RC : CategoryTheory.Bundled Ring


structure FilModCat where
  Mod : ModuleCat R
  -- carrier : Type v
  -- [isAddCommGroup : AddCommGroup carrier]
  -- [isModule : Module R carrier]
  fil : ι → Submodule R Mod
  [f : FilteredModule F Mod fil]
  -- mono : ∀ i ≤ j, fil i ≤ fil j
  -- smul_mem : ∀ i j, (F i : Set R) • fil j ≤ fil (i + j)

instance : Category (FilModCat R F) where
  Hom M N := {f : M.Mod →ₗ[R] N.Mod // ∀ i, f '' M.fil i ≤ N.fil i}
  id _ := ⟨LinearMap.id, by intro i; simp⟩
  comp f g := ⟨g.1.comp f.1, by
    intro i
    have aux1 := f.2 i
    have aux2 := g.2 i
    simp_all only [Set.le_eq_subset, Set.image_subset_iff, LinearMap.coe_comp, Function.comp_apply]
    exact fun _ hx ↦ aux2 <| aux1 hx⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc f g h := rfl

instance {M N : FilModCat R F} : FunLike (M ⟶ N) M.1 N.1 where
  coe f := f.1.toFun
  coe_injective' f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective'
    exact h



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



instance {M N : ModuleCat.{v} R} : AddCommGroup (M ⟶ N) := LinearMap.addCommGroup

instance : Preadditive (ModuleCat.{v} R) where
  add_comp P Q R f f' g := by
    ext
    dsimp
    erw [map_add]
    rfl


-/
