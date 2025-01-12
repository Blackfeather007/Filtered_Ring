import FilteredRing.Basic
import FilteredRing.Filtration_to_Grading

variable {R : Type u} [CommRing R] {A : Type w} [Ring A] [Algebra R A] {ι : Type v}
  [OrderedCancelAddCommMonoid ι] [DecidableEq ι] (𝒜 : ι → Submodule R A) [FilteredAlgebra 𝒜]

local notation3 "f" => (fun i ↦ (𝒜 i).toAddSubgroup)

instance : FilteredRing f := {
  mono := fun {i j} i_le_j ↦ by
    show 𝒜 i ≤ 𝒜 j
    exact FilteredRing.mono i_le_j
  one := by
    show 1 ∈ 𝒜 0
    exact FilteredRing.one
  mul_mem := fun {i j x y} hx hy ↦ by
    show x * y ∈ 𝒜 (i + j)
    exact FilteredRing.mul_mem hx hy
}

noncomputable instance (i : ι) : Module R (GradedPiece f i) where
  smul := by
    intro r x
    set a := Quotient.out' x
    simp only [Submodule.mem_toAddSubgroup] at a
    use QuotientAddGroup.mk (r • a : f i)
  one_smul := sorry
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := by
    intro x
    simp only [HSMul.hSMul, eq_mp_eq_cast, cast_eq, QuotientAddGroup.eq_zero_iff]

    set a := Quotient.out' x with ha

    #check @zero_smul R (𝒜 i) _ _ _ a
    #check @Module.zero_smul R (𝒜 i) _ _ _ a
    have : @SMul.smul R (𝒜 i) (𝒜 i).smul 0 a = 0 := sorry
      -- rw [@zero_smul R (𝒜 i) _ _ _ a]
    simpa [this] using AddSubgroup.zero_mem (Filtration.LTSubgroup f i)

instance : DirectSum.GAlgebra R (GradedPiece f) := sorry
