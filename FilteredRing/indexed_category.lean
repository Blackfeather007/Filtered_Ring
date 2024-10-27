import Mathlib

universe o u v w

open Pointwise CategoryTheory

variable (R : Type u) (ι : Type v) [Ring R] {σ : Type o}

structure IndexedModuleCat where
  Mod : ModuleCat.{w, u} R
  {σMod : Type*}
  [instSetLike : SetLike σMod Mod.carrier]
  [instAddSubmonoidClass : AddSubmonoidClass σMod Mod.carrier]
  ind : ι → σMod

attribute [instance] IndexedModuleCat.instSetLike IndexedModuleCat.instAddSubmonoidClass

instance IndexedModuleSubmonoid {M : IndexedModuleCat R ι} (i : ι) : AddSubmonoid M.Mod where
  carrier := Set.range (AddSubmonoidClass.subtype (M.ind i))
  add_mem' {a b} ha hb := by
    rw [AddSubmonoidClass.coe_subtype, Subtype.range_coe_subtype, Set.mem_setOf_eq] at *
    exact add_mem ha hb
  zero_mem' := by
    show 0 ∈ Set.range ⇑(AddSubmonoidClass.subtype (M.ind i))
    rw [AddSubmonoidClass.coe_subtype, Subtype.range_coe_subtype, Set.mem_setOf_eq]
    exact zero_mem (M.ind i)

instance IndexedModuleCategory : Category (IndexedModuleCat R ι) where
  Hom M N := {f : M.Mod →ₗ[R] N.Mod //
    ∀ i, f '' Set.range (AddSubmonoidClass.subtype (M.ind i))
    ≤ Set.range (AddSubmonoidClass.subtype (N.ind i))}
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

instance IndexedModuleFunLike {M N : IndexedModuleCat R ι} : FunLike (M ⟶ N) M.1 N.1 where
  coe f := f.1.toFun
  coe_injective' _ _ h := propext Subtype.val_inj |>.symm.mpr <| DFunLike.coe_injective' h

instance IndexedModuleConcreteCategory : ConcreteCategory (IndexedModuleCat R ι) where
  forget :=
    { obj := fun R ↦ R.Mod
      map := fun f ↦ f.val }
  forget_faithful := ⟨fun {_ _} ⦃_ _⦄ ht ↦ Subtype.val_inj.mp (LinearMap.ext_iff.mpr (congrFun ht))⟩

@[simp] lemma forget_map {M N : IndexedModuleCat R ι} (f : M ⟶ N) :
  (forget <| IndexedModuleCat R ι).map f = (f : M.Mod → N.Mod) := rfl

def of {X : Type w} [AddCommGroup X] [Module R X] {σX : Type*} [SetLike σX X]
  [AddSubmonoidClass σX X] (indX : ι → σX) : IndexedModuleCat R ι where
    Mod := ModuleCat.of R X
    σMod := σX
    instAddSubmonoidClass := by trivial
    ind := indX

@[simp] theorem of_coe (X : IndexedModuleCat R ι) : of R ι X.ind = X := rfl

@[simp] theorem coe_of (X : Type w) [AddCommGroup X] [Module R X] {σX : Type*} [SetLike σX X]
  [AddSubmonoidClass σX X] (indX : ι → σX) : (of R ι indX).1 = X := rfl

def ofHom {X Y : Type w} {σX σY : Type o} [AddCommGroup X] [Module R X] [SetLike σX X]
  [AddSubmonoidClass σX X] (indX : ι → σX) [AddCommGroup Y] [Module R Y]
  [SetLike σY Y] [AddSubmonoidClass σY Y] (indY : ι → σY) (f : X →ₗ[R] Y)
  (deg0 : ∀ i, f '' Set.range (AddSubmonoidClass.subtype (indX i))
    ≤ Set.range (AddSubmonoidClass.subtype (indY i))) :
    (of R ι indX) ⟶ (of R ι indY) :=
    ⟨f, deg0⟩

theorem ofHom_apply {X Y : Type w} {σX σY : Type o} [AddCommGroup X] [Module R X] [SetLike σX X]
  [AddSubmonoidClass σX X] (indX : ι → σX) [AddCommGroup Y] [Module R Y]
  [SetLike σY Y] [AddSubmonoidClass σY Y] (indY : ι → σY) (f : X →ₗ[R] Y)
  (deg0 : ∀ i, f '' Set.range (AddSubmonoidClass.subtype (indX i))
    ≤ Set.range (AddSubmonoidClass.subtype (indY i))) (x : X) :
  ofHom R ι indX indY f deg0 x = f x := rfl

@[simps]
def ofSelfIso (M : IndexedModuleCat R ι) : (of R ι M.ind) ≅ M where
  hom := 𝟙 M
  inv := 𝟙 M

@[simp]
theorem id_apply {M : IndexedModuleCat R ι} (m : M.1) : (𝟙 M : M.1 → M.1) m = m := rfl

@[simp]
theorem coe_comp {M N U : IndexedModuleCat R ι} (f : M ⟶ N) (g : N ⟶ U) :
  (f ≫ g : M.1 → U.1) = g ∘ f := rfl

private instance {M N : IndexedModuleCat R ι} : AddSemigroup (M ⟶ N) where
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

private instance {M N : IndexedModuleCat R ι} : AddCommMonoid (M ⟶ N) where
  zero := ⟨0, fun i ↦ by
    simp only [Set.le_eq_subset]
    repeat rw [AddSubmonoidClass.coe_subtype, Subtype.range_coe_subtype]
    rw [Set.image_subset_iff]
    exact fun a _ ↦ zero_mem (N.ind i)⟩
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

private instance {M N : IndexedModuleCat R ι} [AddSubgroupClass N.σMod N.Mod.carrier] :
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

instance AddCommGroupMorphisms {M N : IndexedModuleCat R ι} [AddSubgroupClass N.σMod N.Mod.carrier] :
  AddCommGroup (M ⟶ N) where
  neg_add_cancel f := propext Subtype.val_inj |>.symm.mpr
    <| neg_add_cancel f.1
  add_comm := AddCommMagma.add_comm

instance IndexedModulePreadditive (h : ∀ P : IndexedModuleCat R ι, AddSubgroupClass P.σMod P.Mod.carrier) :
  Preadditive (IndexedModuleCat R ι) where
  add_comp P Q R f f' g := by
    exact propext Subtype.val_inj |>.symm.mpr <| LinearMap.comp_add f.1 f'.1 g.1
