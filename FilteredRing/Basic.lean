import Mathlib

universe u v w

variable {R : Type u} {ι : Type v} [Ring R] [OrderedAddCommMonoid ι]

class FilteredRing (F : ι → AddSubgroup R) where
  mono : ∀ i ≤ j, F i ≤ F j
  one : 1 ∈ F 0
  mul_mem : ∀ {i j x y}, x ∈ F i → y ∈ F j → x * y ∈ F (i + j)

variable (F : ι → AddSubgroup R) [fil : FilteredRing F]
variable (M : Type w) [AddCommGroup M] [Module R M]

class FilteredModule (F' : ι → Submodule R M) where
  mono : ∀ i ≤ j, F' i ≤ F' j
  smul_mem : ∀ {i j x y}, x ∈ F i → y ∈ F' j → x • y ∈ F' (i + j)

variable {F} in
def F0 : Subring R where
  __ := F 0
  mul_mem' := by
    intro a b ha hb
    have := fil.mul_mem ha hb
    rw [zero_add] at this
    exact this
  one_mem' := fil.one

instance : Semiring (F 0) := inferInstanceAs (Semiring F0)

instance Module_of_zero_fil (i : ι) : Module (F 0) (F i) where
  smul := fun x y ↦ ⟨x * y, by
    have := fil.mul_mem (SetLike.coe_mem x) (SetLike.coe_mem y)
    rw [zero_add] at this
    exact this⟩
  one_smul := fun x ↦ SetLike.coe_eq_coe.mp (one_mul (x : R))
  mul_smul := fun x y a ↦ SetLike.coe_eq_coe.mp (mul_assoc (x : R) y a)
  smul_zero := fun x ↦ SetLike.coe_eq_coe.mp (mul_zero (x : R))
  smul_add := fun x a b ↦ SetLike.coe_eq_coe.mp (LeftDistribClass.left_distrib (x : R) a b)
  add_smul := fun x y a ↦ SetLike.coe_eq_coe.mp (RightDistribClass.right_distrib (x : R) y a)
  zero_smul := fun x ↦ SetLike.coe_eq_coe.mp (zero_mul (x : R))

instance fil_one_mem (i : ι) (hi : 0 ≤ i) : 1 ∈ F i := (fil.mono 0 hi) fil.one
