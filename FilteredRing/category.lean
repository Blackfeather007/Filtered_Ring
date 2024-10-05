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
    rename_i X Y Z
    have aux1 := f.2 i
    have aux2 := g.2 i
    simp_all only [Set.le_eq_subset, Set.image_subset_iff, LinearMap.coe_comp, Function.comp_apply]
    exact fun _ hx ↦ aux2 <| aux1 hx⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc f g h := rfl
