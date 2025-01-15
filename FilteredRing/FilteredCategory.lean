import FilteredRing.Basic

universe o u v w

namespace Indexed

variable {M γ σ : Type*} (gen : ι → γ) (F' : ι → σ) [Preorder γ] [SetLike σ M] (le : σ →o γ)

class closure : Prop where
  contains : ∀ i : ι, gen i ≤ le.toFun (F' i)
  closure : ∀ s : σ, gen i ≤ le.toFun s → F' i ≤ s

theorem closure_le [closure gen F' le] : F' i ≤ K ↔ gen i ≤ le.toFun K :=
  ⟨fun h ↦ le_trans (closure.contains i) (le.monotone' h), fun h ↦ closure.closure K h⟩

theorem mem_closure [closure gen F' le] : x ∈ F' i ↔ ∀ K, gen i ≤ le.toFun K → x ∈ K :=
  ⟨fun h K hK ↦ (closure.closure K hK) h, fun h ↦ h (F' i) <| closure.contains i⟩

end Indexed

namespace FilteredModule

open CategoryTheory Subtype

variable {R : Type u} {ι : Type v} [Ring R] [OrderedAddCommMonoid ι] {σ : Type o}
  [SetLike σ R] (F : ι → σ) (F_lt : outParam <| ι → σ) [IsRingFiltration F F_lt]

structure FilteredModuleCat where
  Mod : ModuleCat.{w, u} R
  {σMod : Type*}
  [instSetLike : SetLike σMod Mod.carrier]
  [instAddSubgroupClass : AddSubgroupClass σMod Mod.carrier]
  fil : ι → σMod
  fil_lt : ι → σMod
  [instIsModuleFiltration : IsModuleFiltration F F_lt fil fil_lt]

attribute [instance] FilteredModuleCat.instSetLike FilteredModuleCat.instAddSubgroupClass FilteredModuleCat.instIsModuleFiltration

instance : Category (FilteredModuleCat F F_lt) where
  Hom M N := {f : M.Mod →ₗ[R] N.Mod // ∀ (i : ι) (x : M.fil i), f x ∈ N.fil i}
  id _ := ⟨LinearMap.id, fun i x ↦ by
    simp only [LinearMap.id_coe, id_eq, SetLike.coe_mem]⟩
  comp f g := ⟨g.1.comp f.1, fun i x ↦ g.2 i ⟨f.1 x, f.2 i x⟩⟩

instance {M N : FilteredModuleCat F F_lt} : FunLike (M ⟶ N) M.1 N.1 where
  coe f := f.1.toFun
  coe_injective' _ _ h := val_inj.1 <| DFunLike.coe_injective' h

instance : ConcreteCategory (FilteredModuleCat F F_lt) where
  forget :=
    { obj := fun R ↦ R.Mod
      map := fun f ↦ f.val }
  forget_faithful := ⟨fun {_ _} ⦃_ _⦄ ht ↦ val_inj.mp <| LinearMap.ext_iff.mpr
    <| congrFun ht⟩

private instance {M N : FilteredModuleCat F F_lt} : AddSemigroup (M ⟶ N) where
  add f g := ⟨f.1 + g.1, fun i x ↦ add_mem (f.2 i x) (g.2 i x)⟩
  add_assoc a b c := val_inj.1 <| add_assoc a.1 b.1 c.1

private instance {M N : FilteredModuleCat F F_lt} : AddCommMonoid (M ⟶ N) where
  zero := ⟨0, fun i _ ↦ zero_mem (N.fil i)⟩
  zero_add a := val_inj.1 <| zero_add a.1
  add_zero a := val_inj.1 <| add_zero a.1
  nsmul n a := ⟨n • a.1, fun i x ↦ nsmul_mem (a.2 i x) n⟩
  nsmul_zero f := by simp only [zero_smul]; rfl
  nsmul_succ n a := val_inj.1 <| succ_nsmul a.1 n
  add_comm a b := val_inj.1 <| add_comm a.1 b.1

private instance {M N : FilteredModuleCat F F_lt} : SubNegMonoid (M ⟶ N) where
  neg a := ⟨-a.1, fun i x ↦ neg_mem (a.2 i x)⟩
  zsmul z a := ⟨z • a.1, fun i x ↦ zsmul_mem (a.2 i x) z⟩
  zsmul_zero' a := by simp only [zero_smul]; rfl
  zsmul_succ' n a := by
    simp only [Nat.succ_eq_add_one, Int.ofNat_eq_coe, Nat.cast_add, Nat.cast_one, natCast_zsmul]
    apply val_inj.1
    show (((n : ℤ) + 1) • a.1) = (n • a.1 + a.1)
    rw [add_smul, one_smul, natCast_zsmul]
  zsmul_neg' z a := by
    simp only [negSucc_zsmul, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
    apply val_inj.1
    show -((z + 1) • a.1) = -(((z : ℤ) + 1) • a.1)
    rw [add_smul, add_smul, natCast_zsmul, one_smul, one_smul]

instance {M N : FilteredModuleCat F F_lt} : AddCommGroup (M ⟶ N) where
  neg_add_cancel f := val_inj.1 <| neg_add_cancel f.1
  add_comm := AddCommMagma.add_comm

end FilteredModule

namespace Induced

variable {R : Type u} {ι : Type v} [Ring R] {σ : Type o}
  [SetLike σ R] (F : ι → σ) (F_lt : outParam <| ι → σ)
variable {M : ModuleCat.{w, u} R} {σMod : Type*} [SetLike σMod M.1] (F' : ι → σMod)

abbrev closure := Indexed.closure (fun i ↦ {x | ∃ r ∈ F i, ∃ a : M.1, x = r • a})
  F' (⟨fun s ↦ s, fun ⦃_ _⦄ a ↦ a⟩ : σMod →o Set M)

theorem closure_le [closure F F'] : F' i ≤ K ↔ {x | ∃ r ∈ F i, ∃ a : M.1, x = r • a} ⊆ K :=
  Indexed.closure_le (fun i ↦ {x | ∃ r ∈ F i, ∃ a : M.1, x = r • a}) F'
    (⟨fun s ↦ s, fun ⦃_ _⦄ a ↦ a⟩ : σMod →o Set M)

theorem mem_closure [closure F F'] : x ∈ F' i ↔
    ∀ (K : σMod), {x | ∃ r ∈ F i, ∃ a : M.1, x = r • a} ⊆ K → x ∈ K :=
  Indexed.mem_closure (fun i ↦ {x | ∃ r ∈ F i, ∃ a : M.1, x = r • a}) F'
    (⟨fun s ↦ s, fun ⦃_ _⦄ a ↦ a⟩ : σMod →o Set M)

end Induced

namespace AddSubgroup

variable {R : Type u} {ι : Type v} [Ring R] [OrderedAddCommMonoid ι] {σ : Type o}
  [SetLike σ R] (F : ι → σ) (F_lt : outParam <| ι → σ) [IsRingFiltration F F_lt]
  {M : ModuleCat.{w, u} R}

variable (F' : ι → AddSubgroup M.1) (F'_lt : outParam <| ι → AddSubgroup M.1)
  [Induced.closure F F'] [IsFiltration F' F'_lt]

private def preimage_group (i j : ι) (x : R) : AddSubgroup M := {
  carrier := {z | x • z ∈ F' (j + i)}
  add_mem' := fun {a b} ha hb ↦ by
    simp only [Set.mem_setOf_eq, smul_add] at ha hb ⊢
    exact AddSubgroup.add_mem_cancel_right (F' (j + i)) hb |>.2 ha
  zero_mem' := by
    simp only [Set.mem_setOf_eq, smul_zero]
    exact zero_mem (F' (j + i))
  neg_mem' := by
    simp only [Set.mem_setOf_eq, smul_neg, neg_mem_iff, imp_self, implies_true]
}

instance ModuleFiltration : IsModuleFiltration F F_lt F' F'_lt where
  smul_mem {i j x y} hx hy := by
    have : F' j ≤ preimage_group F' j i x := by
      refine Induced.closure_le F F' |>.2 <| fun h ⟨r', hr', ⟨a, ha⟩⟩ ↦ ?_
      refine Induced.mem_closure F F' |>.2 <| fun K hK ↦ ?_
      rw [ha, smul_smul]
      have : (x * r') • a ∈ {x | ∃ r ∈ F (i + j), ∃ a, x = r • a} :=
        ⟨(x * r'), ⟨IsRingFiltration.mul_mem hx hr', ⟨a, rfl⟩⟩⟩
      exact hK this
    have : y ∈ {z | x • z ∈ F' (i + j)} := this hy
    rwa [Set.mem_setOf_eq] at this

end AddSubgroup

namespace Submodule

variable {R : Type u} [CommRing R] {σ : Type o} [SetLike σ R] (F : ι → σ)
  (F_lt : outParam <| ι → σ) [OrderedAddCommMonoid ι]
  [IsRingFiltration F F_lt] {M : ModuleCat.{w, u} R} (F' : ι → Submodule R M.1)
  (F'_lt : outParam <| ι → Submodule R M.1)

variable [Induced.closure F F'] [IsFiltration F' F'_lt]

private def preimage_module (i j : ι) (x : R) : Submodule R M := {
  carrier := {z | x • z ∈ F' (j + i)}
  add_mem' := fun {a b} ha hb ↦ by
    simpa only [Set.mem_setOf_eq, smul_add] using (Submodule.add_mem_iff_right (F' (j + i)) ha).2 hb
  zero_mem' := by simpa only [Set.mem_setOf_eq, smul_zero] using zero_mem (F' (j + i))
  smul_mem' := fun r m hm ↦ by
    rw [Set.mem_setOf_eq, ← smul_assoc, smul_eq_mul, mul_comm, mul_smul]
    exact (Submodule.smul_mem (F' (j + i)) r hm)
}

instance ModuleFiltration : IsModuleFiltration F F_lt F' F'_lt where
  smul_mem {i j x y} hx hy := by
    have : F' j ≤ preimage_module F' j i x := by
      refine Induced.closure_le F F' |>.2 <| fun h ⟨r', hr', ⟨a, ha⟩⟩ ↦ ?_
      refine Induced.mem_closure F F' |>.2 <| fun K hK ↦ ?_
      rw [ha, smul_smul]
      have : (x * r') • a ∈ {x | ∃ r ∈ F (i + j), ∃ a, x = r • a} :=
        ⟨(x * r'), ⟨IsRingFiltration.mul_mem hx hr', ⟨a, rfl⟩⟩⟩
      exact hK this
    have : y ∈ {z | x • z ∈ F' (i + j)} := this hy
    rwa [Set.mem_setOf_eq] at this

end Submodule

namespace Functor

variable {R : Type u} {ι : Type v} [Ring R] [OrderedAddCommMonoid ι] (F : ι → AddSubgroup R) (F_lt : outParam <| ι → AddSubgroup R) [IsRingFiltration F F_lt]

open AddSubgroup

private def F' {M : ModuleCat R} : ι → AddSubgroup M :=
  fun i ↦ closure {x : M | ∃ r ∈ F i, ∃ a : M, x = r • a}

private def F'_lt {M : ModuleCat R} : ι → AddSubgroup M :=
  fun i ↦ closure {x : M | ∃ r ∈ F_lt i, ∃ a : M, x = r • a}

instance {M : ModuleCat R} : IsFiltration (F' F) (F'_lt F_lt) (σ := AddSubgroup M) where
  mono {i j} hij := by
    refine closure_mono <| fun x hx ↦ ?_
    have mono := IsFiltration.mono hij (F := F) (F_lt := F_lt) (A := R)
    obtain ⟨r, hr⟩ := hx
    exact ⟨r, ⟨mono hr.1, hr.2⟩⟩
  is_le {j i} hij := by
    refine closure_mono <| fun x hx ↦ ?_
    have is_le := IsFiltration.is_le hij (F := F) (F_lt := F_lt) (A := R)
    obtain ⟨r, hr⟩ := hx
    exact ⟨r, ⟨is_le hr.1, hr.2⟩⟩
  is_sup B j hij := by
    unfold F'_lt
    replace hij : ∀ i < j, {x | ∃ r ∈ F i, ∃ a, x = r • a} ⊆ B.carrier :=
      fun i hi ↦ (closure_le B).1 (hij i hi)
    rw [closure_le, flt_unfold F F_lt]
    intro x ⟨r, ⟨hr, ⟨a, ha⟩⟩⟩
    rw [ha]
    set preimage : AddSubgroup R := {
      carrier := { s : R | s • a ∈ B}
      add_mem' := fun {a₁ a₂} ha₁ ha₂ ↦ by
        rw [Set.mem_setOf_eq, add_smul]; exact add_mem ha₁ ha₂
      zero_mem' := by
        rw [Set.mem_setOf_eq, zero_smul]; exact zero_mem B
      neg_mem' := fun {x} hx ↦ by
        rw [Set.mem_setOf_eq, neg_smul]; exact neg_mem hx
    } with preimage_def
    suffices ⨆ i, ⨆ (_ : i < j), F i ≤ preimage from this hr
    refine iSup_le <| fun i ↦ iSup_le <| fun hij' r' hr' ↦ ?_
    rw [preimage_def]
    replace hij := hij i hij'
    have : r' • a ∈ {x | ∃ r ∈ F i, ∃ a, x = r • a} := ⟨r', ⟨hr', ⟨a, rfl⟩⟩⟩
    exact hij this

instance {M : ModuleCat R} : Induced.closure F (F' F) (M := M) where
  contains i := closure_le (F' F i) |>.1 <| by rfl
  closure {i} s hs := closure_le s |>.2 hs

open FilteredModule

def DeducedFunctor : CategoryTheory.Functor (ModuleCat.{w, u} R)
  (FilteredModuleCat F F_lt) where
  obj m := {
    Mod := m
    σMod := AddSubgroup m
    fil := F' F
    fil_lt := F'_lt F_lt
  }
  map := fun {X Y} hom ↦ ⟨hom, by
    intro i p y hy
    obtain ⟨y', hy'⟩ := hy
    have inter : ∀ a, a ∈ ⋂ (_ : {z | ∃ r ∈ F i, ∃ a, z = r • a} ⊆ y'.carrier), y'
      ↔ a ∈ y := fun a ↦ Eq.to_iff (congrFun hy' a)
    simp only [Set.mem_iInter, AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
      mem_toAddSubmonoid] at inter
    replace inter := inter (hom p)
    refine inter.1 (fun h ↦ ?_)
    set map_group := (closure {x : Y.1 | ∃ r ∈ F i, ∃ a, x = r • a}).comap hom.toAddMonoidHom
      with map_group_def
    have le := (closure_le y').2 h
    suffices p.1 ∈ map_group from le this
    suffices closure {z : X.1 | ∃ r ∈ F i, ∃ a, z = r • a} ≤ map_group from this p.2
    suffices hpre : {x : X.1 | ∃ r ∈ F i, ∃ a, x = r • a} ⊆ hom ⁻¹' {x : Y.1 | ∃ r ∈ F i, ∃ a, x = r • a} from by
      refine (closure_le map_group).2 (fun x hx ↦ ?_)
      obtain ⟨r, ⟨hr, ⟨a, rfl⟩⟩⟩ := hx
      rw [map_group_def]
      simp only [coe_comap, LinearMap.toAddMonoidHom_coe, Set.mem_preimage, map_smul,
        SetLike.mem_coe]
      suffices r • hom a ∈ {x | ∃ r ∈ F i, ∃ a, x = r • a} from
        mem_closure.2 (fun K hK ↦ hK this)
      rw [← map_smul]
      have in_pre := hpre ⟨r, ⟨hr, ⟨a, rfl⟩⟩⟩
      exact in_pre
    intro x hx
    obtain ⟨r, ⟨hr, ⟨a, rfl⟩⟩⟩ := hx
    exact ⟨r, ⟨hr, ⟨hom a, map_smul hom r a⟩⟩⟩⟩

end Functor
