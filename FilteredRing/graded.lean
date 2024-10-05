import FilteredRing.Basic

open AddSubgroup
open Pointwise

variable {R : Type u} [Ring R]

variable {ι : Type v} [OrderedAddCommMonoid ι] [DecidableEq ι] [PredOrder ι]

variable (F : ι → AddSubgroup R) [FilteredRing F]

instance {i : ι}: F (PredOrder.pred i) ≤ F i :=
  FilteredRing.mono (PredOrder.pred i) (PredOrder.pred_le i)

def gradedMap {i : ι} := ((F i) ⧸ (F (PredOrder.pred i)).addSubgroupOf (F i))

instance : GradedRing (F) where--It may be not correct,attention!
  one_mem := FilteredRing.one
  mul_mem := by
    intro i j x y hx hy
    have t1 : (F i : Set R) * F j ≤ F (i + j) := FilteredRing.mul_mem i j
    have t2 : x * y ∈ (F i : Set R) * F j := Set.mul_mem_mul hx hy
    exact t1 t2
  decompose' := by
    intro r

    sorry
  left_inv := sorry
  right_inv := sorry
