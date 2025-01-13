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

instance : Category (FilteredModuleCat F F_lt) where
  Hom M N := {f : M.Mod →ₗ[R] N.Mod //
    ∀ i, f '' Set.range (AddSubmonoidClass.subtype (M.fil i))
    ≤ Set.range (AddSubmonoidClass.subtype (N.fil i))}
  id _ := ⟨LinearMap.id, fun i ↦ by
    simp only [LinearMap.id_coe, id_eq, Set.image_id', le_refl]⟩
  comp f g := ⟨g.1.comp f.1, fun i ↦ by
    have aux1 := f.2 i
    have aux2 := g.2 i
    simp only [Set.le_eq_subset, Set.image_subset_iff] at aux1 aux2 ⊢
    exact fun _ hx ↦ aux2 <| aux1 hx⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

instance {M N : FilteredModuleCat F F_lt} : FunLike (M ⟶ N) M.1 N.1 where
  coe f := f.1.toFun
  coe_injective' _ _ h := Subtype.val_inj.1 <| DFunLike.coe_injective' h

instance {M N : FilteredModuleCat F F_lt} [AddSubmonoidClass N.σMod N.Mod.carrier] :
  AddCommMonoid (M ⟶ N) where
    add := fun f g ↦ ⟨f.1 + g.1, fun i x hx ↦ by
      rw [AddSubmonoidClass.coe_subtype, Subtype.range_coe_subtype] at hx ⊢
      obtain ⟨x', hx'⟩ := hx
      have f2 := f.2 i
      simp only [AddSubmonoidClass.coe_subtype, Set.le_eq_subset, Subtype.range_coe_subtype,
        Set.image_subset_iff, Set.preimage_setOf_eq, Set.setOf_subset_setOf] at f2
      have g2 := g.2 i
      simp only [AddSubmonoidClass.coe_subtype, Set.le_eq_subset, Subtype.range_coe_subtype,
        Set.image_subset_iff, Set.preimage_setOf_eq, Set.setOf_subset_setOf] at g2
      rw [Set.mem_setOf_eq, ← hx'.2]
      exact add_mem (f2 x' hx'.1) (g2 x' hx'.1)⟩
    add_assoc a b c := by
      apply DFunLike.coe_injective'
      funext x
      show ((a.1 + b.1) + c.1) x = (a.1 + (b.1 + c.1)) x
      exact add_assoc (a.1 x) (b.1 x) (c.1 x)
    zero := ⟨0, by
      simp only [LinearMap.zero_apply, AddSubmonoidClass.coe_subtype,
        Subtype.range_coe_subtype, Set.le_eq_subset, Set.image_subset_iff, Set.preimage_setOf_eq,
        Set.setOf_subset_setOf]
      exact fun i _ _ ↦ zero_mem (fil i)⟩
    zero_add a := by
      apply DFunLike.coe_injective'
      funext x
      show (0 + a.1) x = a.1 x
      exact zero_add (a.1 x)
    add_zero a := by
      apply DFunLike.coe_injective'
      funext x
      show (a.1 + 0) x = a.1 x
      exact add_zero (a.1 x)
    nsmul n a := ⟨n • a.1, fun i x hx ↦ by
      rw [AddSubmonoidClass.coe_subtype, Subtype.range_coe_subtype] at hx ⊢
      obtain ⟨x', hx'⟩ := hx
      have a2 := a.2 i
      simp only [AddSubmonoidClass.coe_subtype, Set.le_eq_subset, Subtype.range_coe_subtype,
        Set.image_subset_iff, Set.preimage_setOf_eq, Set.setOf_subset_setOf] at a2
      rw [← hx'.2]
      exact nsmul_mem (a2 x' hx'.1) n⟩
    add_comm a b := by
      apply DFunLike.coe_injective'
      funext x
      show (a.1 + b.1) x = (b.1 + a.1) x
      exact AddCommMagma.add_comm (a.1 x) (b.1 x)
    nsmul_zero x := by
      simp only [AddSubmonoidClass.coe_subtype, Set.le_eq_subset, zero_smul]
      exact rfl
    nsmul_succ n x := by
      apply DFunLike.coe_injective'
      funext x'
      show ((n + 1) • x.1) x' = (n • x.1 + x.1) x'
      exact succ_nsmul (x.1 x') n

end FilteredModuleCat
