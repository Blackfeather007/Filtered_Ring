import FilteredRing.Basic

open AddSubgroup
variable {R : Type u} [Ring R]

variable {ι : Type v} [OrderedAddCommMonoid ι] [DecidableEq ι] [PredOrder ι]

variable (F : ι → AddSubgroup R) [FilteredRing F]

instance {i : ι}: F (PredOrder.pred i) ≤ F i :=
  FilteredRing.mono (PredOrder.pred i) (PredOrder.pred_le i)

def gradedMap {i : ι} : Module R ((F i) ⧸ (F (PredOrder.pred i)).addSubgroupOf (F i)) := sorry

-- instance : GradedRing (gradedMap F) := sorry
