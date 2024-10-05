import FilteredRing.Basic

open AddSubgroup
variable {R : Type u} [Ring R]

variable {ι : Type v} [OrderedAddCommMonoid ι] [DecidableEq ι] [PredOrder ι]

variable (F : ι → AddSubgroup R) [FilteredRing F]


def gradedMap (F : ι → AddSubgroup R) [FilteredRing F] : ι → AddSubgroup R := sorry

instance : GradedRing (gradedMap F) := sorry
