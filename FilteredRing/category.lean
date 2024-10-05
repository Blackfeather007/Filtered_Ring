import FilteredRing.Basic
open Pointwise CategoryTheory

variable (R : Type u) {ι : Type v} [Ring R] [OrderedAddCommMonoid ι] [DecidableEq ι]
variable (F : ι → AddSubgroup R)
-- instance RC : CategoryTheory.Bundled Ring


structure FilModCat where
  M : ModuleCat R
  -- carrier : Type v
  -- [isAddCommGroup : AddCommGroup carrier]
  -- [isModule : Module R carrier]
  fil : ι → Submodule R M
  [f :FilteredModule F M fil]
  -- mono : ∀ i ≤ j, fil i ≤ fil j
  -- smul_mem : ∀ i j, (F i : Set R) • fil j ≤ fil (i + j)

instance : Category (FilModCat R F) where
  Hom := sorry
  id := sorry
  comp := sorry
  id_comp := sorry
  comp_id := sorry
  assoc := sorry
