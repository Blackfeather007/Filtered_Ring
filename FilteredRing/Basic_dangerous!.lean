import Mathlib

universe u v w

variable {R : Type u} {ιR : Type v} [Ring R] [OrderedAddCommMonoid ιR] [DecidableRel LE.le (α := ιR)]


section FilteredRing

class FilteredRing (F : ιR → AddSubgroup R) where
  mono {i j} : i ≤ j → F i ≤ F j
  one : 1 ∈ F 0
  mul_mem : ∀ {i j x y}, x ∈ F i → y ∈ F j → x * y ∈ F (i + j)

instance trivialRingFiltration (comparable_with_zero : ∀ i : ιR, Decidable (i ≥ 0)) :
  FilteredRing (fun (i : ιR) ↦ if i ≥ 0 then (⊤ : AddSubgroup R) else (⊥ : AddSubgroup R)) where
    mono := by
      intro i j ilej
      by_cases ige0 : i ≥ 0
      · simp only [ge_iff_le, ige0, reduceIte, top_le_iff, Preorder.le_trans 0 i j ige0 ilej]
      · simp only [ge_iff_le, ige0, reduceIte, bot_le]
    one := by simp only [ge_iff_le, le_refl, reduceIte, AddSubgroup.mem_top]
    mul_mem := by
      intro i j x y hx hy
      by_cases ige0 : i ≥ 0
      · by_cases jge0 : j ≥ 0
        · simp only [ge_iff_le, Left.add_nonneg ige0 jge0, reduceIte, AddSubgroup.mem_top]
        · simp only [ge_iff_le, jge0, reduceIte, AddSubgroup.mem_bot] at hy
          simp only [ge_iff_le, hy, mul_zero, AddSubgroup.zero_mem (if 0 ≤ i + j then ⊤ else ⊥)]
      · simp only [ge_iff_le, ige0, reduceIte, AddSubgroup.mem_bot] at hx
        simp only [ge_iff_le, hx, zero_mul, AddSubgroup.zero_mem (if 0 ≤ i + j then ⊤ else ⊥)]

variable (F : ιR → AddSubgroup R) [FilteredRing F]

variable {F} in
private def F0 : Subring R where
  __ := F 0
  mul_mem' hx hy := by simpa [zero_add] using FilteredRing.mul_mem hx hy
  one_mem' := FilteredRing.one

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

variable (F : ιR → AddSubgroup R) [FilteredRing F]

variable {M : Type w} {ιM : Type v} [OrderedAddCommMonoid ιM] [VAdd ιR ιM] [AddCommGroup M] [Module R M]

class FilteredModule (F' : ιM → AddSubgroup M) where
  mono : ∀ {i j}, i ≤ j → F' i ≤ F' j
  smul_mem : ∀ {i j x y}, x ∈ F i → y ∈ F' j → x • y ∈ F' (i +ᵥ j)

instance trivialModuleFiltration
  (comparable_with_zeroM : ∀ i : ιM, Decidable (0 ≤ i)) :
    FilteredModule
      (fun (i : ιR) ↦ if 0 ≤ i then (⊤ : AddSubgroup R) else (⊥ : AddSubgroup R))
      (fun (i : ιM) ↦ if 0 ≤ i then (⊤ : AddSubgroup M) else (⊥ : AddSubgroup M)) where
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
      · simp only [ge_iff_le, jge0, reduceIte, AddSubgroup.mem_bot] at hm
        simp only [ge_iff_le, hm, smul_zero, AddSubgroup.zero_mem (if 0 ≤ i +ᵥ j then ⊤ else ⊥)]
    · simp only [ge_iff_le, ige0, reduceIte, AddSubgroup.mem_bot] at hr
      simp only [ge_iff_le, hr, zero_smul, AddSubgroup.zero_mem (if 0 ≤ i +ᵥ j then ⊤ else ⊥)]

variable (M) in
instance trivialModuleFiltration' :
  FilteredModule F (fun (_ : ιM) ↦ (⊤ : AddSubgroup M)) where
    mono := fun {_ _} _ ⦃_⦄ a ↦ a
    smul_mem := fun {_ _} {_} {_} _ a ↦ a

end FilteredModule
