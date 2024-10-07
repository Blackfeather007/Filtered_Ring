import Mathlib

universe u v w

variable {R : Type u} [Semiring R]
variable {ιR : Type v} [OrderedAddCommMonoid ιR] [DecidableRel LE.le (α := ιR)]
variable {σR : Type*} [SetLike σR R] [AddSubmonoidClass σR R]

section FilteredRing

class FilteredRing (F : ιR → σR) where
  mono {i j} : i ≤ j → F i ≤ F j
  one : 1 ∈ F 0
  mul_mem : ∀ {i j x y}, x ∈ F i → y ∈ F j → x * y ∈ F (i + j)

instance trivialRingFiltration :
  FilteredRing (fun (i : ιR) ↦ if i ≥ 0 then (⊤ : AddSubmonoid R) else (⊥ : AddSubmonoid R)) where
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

variable (F : ιR → σR) [FilteredRing F]

variable {F} in
private def F0 : Subsemiring R where
  carrier := F 0
  mul_mem' a b := by simpa [← zero_add 0] using FilteredRing.mul_mem a b
  one_mem' := FilteredRing.one
  add_mem' a b := add_mem a b
  zero_mem' := zero_mem (F 0)

instance : Semiring (F 0) := inferInstanceAs (Semiring F0)

instance Module_of_zero_fil (i : ιR) : Module (F 0) (F i) where
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

variable (F : ιR → σR) [FilteredRing F]

variable {M : Type w} [AddCommMonoid M] [Module R M]
variable {ιM : Type v} [OrderedAddCommMonoid ιM] [DecidableRel LE.le (α := ιM)] [VAdd ιR ιM]
variable {σM : Type*} [SetLike σM M] [AddSubmonoidClass σM M]

class FilteredModule (F' : ιM → σM) where
  mono : ∀ {i j}, i ≤ j → F' i ≤ F' j
  smul_mem : ∀ {i j x y}, x ∈ F i → y ∈ F' j → x • y ∈ F' (i +ᵥ j)

instance trivialModuleFiltration
  (comparable_with_zeroM : ∀ i : ιM, Decidable (0 ≤ i)) :
    FilteredModule
      (fun (i : ιR) ↦ if 0 ≤ i then (⊤ : AddSubmonoid R) else (⊥ : AddSubmonoid R))
      (fun (i : ιM) ↦ if 0 ≤ i then (⊤ : AddSubmonoid M) else (⊥ : AddSubmonoid M)) where
  mono := by
    intro i j ilej
    by_cases ige0 : 0 ≤ i
    · simp only [ge_iff_le, ige0, reduceIte, top_le_iff, Preorder.le_trans 0 i j ige0 ilej]
    · simp only [ge_iff_le, ige0, reduceIte, bot_le]
  smul_mem := by
    intro i j r m hr hm
    by_cases ige0 : 0 ≤ i
    · by_cases jge0 : 0 ≤ j
      · sorry
      · simp only [ge_iff_le, jge0, reduceIte, AddSubmonoid.mem_bot] at hm
        simp only [ge_iff_le, hm, smul_zero, AddSubmonoid.zero_mem (if 0 ≤ i +ᵥ j then ⊤ else ⊥)]
    · simp only [ge_iff_le, ige0, reduceIte, AddSubmonoid.mem_bot] at hr
      simp only [ge_iff_le, hr, zero_smul, AddSubmonoid.zero_mem (if 0 ≤ i +ᵥ j then ⊤ else ⊥)]

variable (M) in
instance trivialModuleFiltration' :
  FilteredModule F (fun (_ : ιM) ↦ (⊤ : AddSubmonoid M)) where
    mono := fun {_ _} _ ⦃_⦄ a ↦ a
    smul_mem := fun {_ _} {_} {_} _ a ↦ a

end FilteredModule
