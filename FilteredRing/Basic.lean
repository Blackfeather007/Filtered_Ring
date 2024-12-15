import Mathlib

universe u v w

variable {R : Type u} {ι : Type v} [Semiring R] [OrderedAddCommMonoid ι] [DecidableEq ι]
  {σ : Type*} [SetLike σ R] [AddSubmonoidClass σ R]

section FilteredRing

class FilteredRing (F : ι → σ) : Prop where
  mono {i j} : i ≤ j → F i ≤ F j
  one : 1 ∈ F 0
  mul_mem : ∀ {i j x y}, x ∈ F i → y ∈ F j → x * y ∈ F (i + j)

instance trivialRingFiltration [DecidableRel LE.le (α := ι)] :
  FilteredRing (fun (i : ι) ↦ if i ≥ 0 then (⊤ : AddSubmonoid R) else (⊥ : AddSubmonoid R)) where
    mono := by
      intro i j ilej
      by_cases ige0 : i ≥ 0
      · simp only [ge_iff_le, ige0, reduceIte, top_le_iff, Preorder.le_trans 0 i j ige0 ilej]
      · simp only [ge_iff_le, ige0, reduceIte, bot_le]
    one := by simp only [ge_iff_le, le_refl, reduceIte, AddSubmonoid.mem_top]
    mul_mem := by
      intro i j x y hx hy
      by_cases ige0 : i ≥ 0
      · by_cases jge0 : j ≥ 0
        · simp only [ge_iff_le, Left.add_nonneg ige0 jge0, reduceIte, AddSubmonoid.mem_top]
        · simp only [ge_iff_le, jge0, reduceIte, AddSubmonoid.mem_bot] at hy
          simp only [ge_iff_le, hy, mul_zero, AddSubmonoid.zero_mem (if 0 ≤ i + j then ⊤ else ⊥)]
      · simp only [ge_iff_le, ige0, reduceIte, AddSubmonoid.mem_bot] at hx
        simp only [ge_iff_le, hx, zero_mul, AddSubmonoid.zero_mem (if 0 ≤ i + j then ⊤ else ⊥)]

variable (F : ι → σ) [FilteredRing F]

variable {F} in
private def F0 : Subsemiring R where
  carrier := F 0
  mul_mem' a b := by simpa [← zero_add 0] using FilteredRing.mul_mem a b
  one_mem' := FilteredRing.one
  add_mem' a b := add_mem a b
  zero_mem' := zero_mem (F 0)

instance : Semiring (F 0) := inferInstanceAs (Semiring F0)

instance Module_of_zero_fil (i : ι) : Module (F 0) (F i) where
  smul := fun x y ↦ ⟨x * y, by
    simpa [zero_add] using FilteredRing.mul_mem (SetLike.coe_mem x) (SetLike.coe_mem y)⟩
  one_smul := fun x ↦ SetLike.coe_eq_coe.mp (one_mul (x : R))
  mul_smul := fun x y a ↦ SetLike.coe_eq_coe.mp (mul_assoc (x : R) y a)
  smul_zero := fun x ↦ SetLike.coe_eq_coe.mp (mul_zero (x : R))
  smul_add := fun x a b ↦ SetLike.coe_eq_coe.mp (LeftDistribClass.left_distrib (x : R) a b)
  add_smul := fun x y a ↦ SetLike.coe_eq_coe.mp (RightDistribClass.right_distrib (x : R) y a)
  zero_smul := fun x ↦ SetLike.coe_eq_coe.mp (zero_mul (x : R))

end FilteredRing


section FilteredModule

variable (F : ι → σ) [FilteredRing F]

variable {M : Type w} [AddCommMonoid M] [Module R M]
variable {ιM : Type v} [OrderedAddCommMonoid ιM] [VAdd ι ιM]
variable {σM : Type*} [SetLike σM M] [AddSubmonoidClass σM M]
--σM is more general, usually σM = σ

class FilteredModule (F' : ιM → σM) : Prop where
  mono : ∀ {i j}, i ≤ j → F' i ≤ F' j
  smul_mem : ∀ {i j x y}, x ∈ F i → y ∈ F' j → x • y ∈ F' (i +ᵥ j)

instance trivialModuleFiltration [DecidableRel LE.le (α := ι)] [DecidableRel LE.le (α := ιM)] :
  FilteredModule (fun (i : ι) ↦ if 0 ≤ i then (⊤ : AddSubmonoid R) else (⊥ : AddSubmonoid R))
  (fun (i : ιM) ↦ if 0 ≤ i then (⊤ : AddSubmonoid M) else (⊥ : AddSubmonoid M)) where
  mono := by
    intro i j ilej
    by_cases ige0 : 0 ≤ i
    · simp only [ge_iff_le, ige0, reduceIte, top_le_iff, Preorder.le_trans 0 i j ige0 ilej]
    · simp only [ge_iff_le, ige0, reduceIte, bot_le]
  smul_mem := by
    intro i j r m hr hm
    by_cases ige0 : i ≥ 0
    · by_cases jge0 : j ≥ 0
      · sorry
      · simp only [ge_iff_le, jge0, reduceIte, AddSubmonoid.mem_bot] at hm
        simp only [hm, smul_zero, AddSubmonoid.zero_mem (if 0 ≤ i +ᵥ j then ⊤ else ⊥)]
    · simp only [ge_iff_le, ige0, reduceIte, AddSubmonoid.mem_bot] at hr
      simp only [ge_iff_le, hr, zero_smul, AddSubmonoid.zero_mem (if 0 ≤ i +ᵥ j then ⊤ else ⊥)]

instance trivialModuleFiltration' : FilteredModule F fun _ : ιM ↦ (⊤ : AddSubmonoid M) where
  mono := fun _ ⦃_⦄ a ↦ a
  smul_mem := fun _ a ↦ a




section FilteredAlgebra

variable {R : Type u} [CommSemiring R] {A : Type w} [Semiring A] [Algebra R A]

variable (𝒜 : ι → Submodule R A)

abbrev FilteredAlgebra := FilteredRing 𝒜

end FilteredAlgebra
