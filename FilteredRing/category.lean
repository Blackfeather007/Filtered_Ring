import FilteredRing.Basic

universe u v w

open Pointwise CategoryTheory

variable {R : Type u} {ι : Type v} [Ring R] [OrderedAddCommMonoid ι]
variable (F : ι → AddSubgroup R)

structure FilteredModuleCat where
  Mod : ModuleCat.{w, u} R
  fil : ι → AddSubgroup Mod.carrier
  [f : FilteredModule F fil]

namespace FilteredModuleCat

instance filteredModuleCategory : Category (FilteredModuleCat F) where
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

instance {M N : FilteredModuleCat F} : FunLike (M ⟶ N) M.1 N.1 where
  coe f := f.1.toFun
  coe_injective' _ _ h := propext Subtype.val_inj |>.symm.mpr <| DFunLike.coe_injective' h

instance filteredModuleConcreteCategory : ConcreteCategory (FilteredModuleCat F) where
  forget :=
    { obj := fun R ↦ R.Mod
      map := fun f ↦ f.val }
  forget_faithful := {
    map_injective := fun {X Y} ⦃t1 t2⦄ ht ↦ Subtype.val_inj.mp (LinearMap.ext_iff.mpr (congrFun ht)) }

@[simp]
lemma forget_map {M N : FilteredModuleCat F} (f : M ⟶ N) :
  (forget (FilteredModuleCat F)).map f = (f : M.Mod → N.Mod) := rfl

/-- The object in the category of R-filt associated to an filtered R-module -/
def of {X : Type w} [AddCommGroup X] [Module R X] (filX : ι → AddSubgroup X)
  [FilteredModule F filX] : FilteredModuleCat F where
    Mod := ModuleCat.of R X
    fil := by simpa only [ModuleCat.coe_of]
    f := by simpa [ModuleCat.coe_of]

instance {X : FilteredModuleCat F} : FilteredModule F X.fil := X.f

@[simp]
theorem of_coe (X : FilteredModuleCat F) : of F X.fil = X := rfl

@[simp]
theorem coe_of (X : Type w) [AddCommGroup X] [Module R X] (filX : ι → AddSubgroup X)
  [FilteredModule F filX] : (of F filX).1 = X := rfl

/-- A `LinearMap` with degree 0 is a morphism in `Module R`. -/
def ofHom {X Y : Type w} [AddCommGroup X] [Module R X] {filX : ι → AddSubgroup X}
  [FilteredModule F filX] [AddCommGroup Y] [Module R Y] {filY : ι → AddSubgroup Y}
  [FilteredModule F filY] (f : X →ₗ[R] Y) (deg0 : ∀ i, f '' filX i ≤ filY i) :
  of F filX ⟶ of F filY :=
    ⟨f, deg0⟩

-- @[simp 1100] ← 有lint错误
theorem ofHom_apply {X Y : Type w} [AddCommGroup X] [Module R X] {filX : ι → AddSubgroup X}
  [FilteredModule F filX] [AddCommGroup Y] [Module R Y] {filY : ι → AddSubgroup Y}
  [FilteredModule F filY] (f : X →ₗ[R] Y) (deg0 : ∀ i, f '' filX i ≤ filY i) (x : X) :
  ofHom F f deg0 x = f x := rfl

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
theorem coe_comp {M N U : FilteredModuleCat F} (f : M ⟶ N) (g : N ⟶ U) : (f ≫ g : M.1 → U.1) = g ∘ f :=
  rfl

private instance {M N : FilteredModuleCat F} : AddSemigroup (M ⟶ N) where
  add f g := ⟨f.1 + g.1, by
    simp only [Set.le_eq_subset, LinearMap.add_apply, Set.image_subset_iff]
    intro i _ hx
    have aux1 := f.2 i
    have aux2 := g.2 i
    simp_all only [SetLike.mem_coe, Set.le_eq_subset, Set.image_subset_iff, Set.mem_preimage]
    exact AddMemClass.add_mem (aux1 hx) (aux2 hx)⟩
  add_assoc a b c := propext Subtype.val_inj |>.symm.mpr
    <| add_assoc a.1 b.1 c.1

private instance {M N : FilteredModuleCat F} : AddMonoid (M ⟶ N) where
  zero := ⟨0, fun i ↦ by simp [AddSubgroup.zero_mem (N.fil i)]⟩
  zero_add a := propext Subtype.val_inj |>.symm.mpr
    <| AddZeroClass.zero_add a.1
  add_zero a := propext Subtype.val_inj |>.symm.mpr
    <| AddZeroClass.add_zero a.1
  nsmul k f := ⟨k • f.1, by
    simp only [Set.le_eq_subset, LinearMap.smul_apply, Set.image_subset_iff]
    intro i _ hx
    have aux := f.2 i
    simp_all only [SetLike.mem_coe, Set.le_eq_subset, Set.image_subset_iff, Set.mem_preimage]
    exact AddSubgroup.nsmul_mem (N.fil i) (aux hx) k⟩
  nsmul_zero _ := by
    simp only [Set.le_eq_subset, zero_smul]; rfl
  nsmul_succ n x := propext Subtype.val_inj |>.symm.mpr
    <| succ_nsmul x.1 n

private instance {M N : FilteredModuleCat F} : SubNegMonoid (M ⟶ N) where
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
    simp only [Nat.succ_eq_add_one, Int.ofNat_eq_coe, Nat.cast_one, Set.le_eq_subset, natCast_zsmul]
    exact succ_nsmul f.1 k
  zsmul_neg' k f := by
    rw [← Subtype.val_inj]
    simp only [Set.le_eq_subset, negSucc_zsmul, Nat.cast_add, Nat.cast_one, neg_inj]
    norm_cast

instance {M N : FilteredModuleCat F} : AddCommGroup (M ⟶ N) where
  neg_add_cancel f := propext Subtype.val_inj |>.symm.mpr
    <| neg_add_cancel f.1
  add_comm f g := propext Subtype.val_inj |>.symm.mpr
    <| AddCommMagma.add_comm f.1 g.1

instance : Preadditive (FilteredModuleCat F) where
  add_comp P Q R f f' g := by
    exact propext Subtype.val_inj |>.symm.mpr <| LinearMap.comp_add f.1 f'.1 g.1

private def F' (m : ModuleCat.{w, u} R) := fun i ↦
  AddSubgroup.closure {x | ∃ r ∈ F i, ∃ a : m.1, x = r • a}

private def proofGP (m : ModuleCat.{w, u} R) (i j : ι) (x : R) : AddSubgroup m.1 := {
  carrier := {z | x • z ∈ F' F m (j + i)}
  add_mem' := fun {a b} ha hb ↦ by
    simp only [F', Set.mem_setOf_eq, smul_add]
    exact (AddSubgroup.add_mem_cancel_right (AddSubgroup.closure
      {x | ∃ r ∈ F (j + i), ∃ a, x = r • a}) hb).mpr ha
  zero_mem' :=
    congrArg (Membership.mem (F' F m (j + i))) (smul_zero x) |>.mpr (F' F m (j + i)).zero_mem
  neg_mem' := by simp only [Set.mem_setOf_eq, smul_neg, neg_mem_iff, imp_self, implies_true] }

open AddSubgroup in
instance toFilteredModule (m : ModuleCat.{w, u} R) [FilteredRing F] : FilteredModule F (F' F m) where
  mono := fun hij ↦ by
    simp only [F', closure_le]
    rintro x ⟨r, ⟨hr, ⟨a, ha⟩⟩⟩
    exact mem_closure.mpr fun K hk ↦ hk <| Exists.intro r ⟨FilteredRing.mono hij hr, Exists.intro a ha⟩
  smul_mem := by
    intro j i x y hx hy
    have : F' F m i ≤ proofGP F m i j x := by
      apply (closure_le <| proofGP F m i j x).mpr
      rintro h ⟨r', hr', ⟨a, ha⟩⟩
      exact ha.symm ▸ mem_closure.mpr fun K hk ↦ hk ⟨x * r', ⟨FilteredRing.mul_mem hx hr', ⟨a, smul_smul x r' a⟩⟩⟩
    exact this hy

open AddSubgroup in
def DeducedFunctor [FilteredRing F] : CategoryTheory.Functor (ModuleCat.{w, u} R) (FilteredModuleCat F) where
  obj m := { Mod := m, fil := F' F m, f := toFilteredModule F m }
  map := fun {X Y} hom ↦ ⟨hom, by
    rintro i p ⟨x, ⟨hx1, hx2⟩⟩
    set toAddGP := (closure {x : Y.1 | ∃ r ∈ F i, ∃ a, x = r • a}).comap hom.toAddMonoidHom
    suffices x ∈ toAddGP from hx2.symm ▸ this
    suffices closure {x : X.1 | ∃ r ∈ F i, ∃ a, x = r • a} ≤ toAddGP from this hx1
    suffices {x : X.1 | ∃ r ∈ F i, ∃ a, x = r • a} ⊆ hom ⁻¹' {x : Y.1 | ∃ r ∈ F i, ∃ a, x = r • a} from
      (propext (closure_le toAddGP)).mpr fun ⦃a⦄ t ↦ subset_closure (this t)
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
