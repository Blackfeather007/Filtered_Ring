import FilteredRing.Basic
import FilteredRing.Filtration_to_Grading

variable {R : Type u} [CommRing R] {A : Type w} [Ring A] [Algebra R A] {ι : Type v}
  [OrderedCancelAddCommMonoid ι] [DecidableEq ι] (𝒜 : ι → Submodule R A) [FilteredAlgebra 𝒜]

instance bur : FilteredRing (fun i ↦ (𝒜 i).toAddSubgroup) := sorry

instance burbur (i : ι) : Module R (GradedPiece (fun i ↦ (𝒜 i).toAddSubgroup) i) := sorry

-- #check GradedPiece fun i ↦ (𝒜 i).toAddSubgroup

instance : DirectSum.GAlgebra R (GradedPiece fun i ↦ (𝒜 i).toAddSubgroup) := sorry
