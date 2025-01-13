import FilteredRing.Basic

section FilteredRing_fil_map_range

variable {ι : Type v} [OrderedCancelAddCommMonoid ι]
{R : Type*} [Ring R] (σR : Type*) [SetLike σR R] [AddSubgroupClass σR R]
{S : Type*} [Ring S] (σS : Type*) [SetLike σS S] [AddSubgroupClass σS S]

class FilteredRingHom (f : R →+* S) where
  map : σR → σS
  image_coe_eq_coe_map (x : σR) : f '' (x : Set R) = map x

variable (FR : ι → σR) (FR_lt : ι → σR) [fil : IsRingFiltration FR FR_lt] (f : R →+* S)
[FilteredRingHom σR σS f]

def filtrationMap (i : ι) : σS :=
  FilteredRingHom.map f (FR i)

/-
instance FilteredRing_fil_map_range : FilteredRing (filring_map FR f) where
  mono := by
    intro i j ilej y hy
    obtain ⟨x, x_in, x_eq⟩ : ∃ x ∈ FR i , f x = y := hy
    use x
    simp only [SetLike.mem_coe, (FilteredRing.mono ilej) x_in, x_eq, and_self]
  one := by
    use 1
    simp only [SetLike.mem_coe, FilteredRing.one, map_one, and_self]
  mul_mem := by
    intro i j x y x_in_i y_in_j
    simp only [filring_map, AddSubgroup.mem_map] at *
    obtain ⟨x₁, x_in, x_eq⟩ := x_in_i
    obtain ⟨y₁, y_in, y_eq⟩ := y_in_j
    use x₁ * y₁
    simp only [FilteredRing.mul_mem x_in y_in, map_mul, x_eq, y_eq, and_self]
-/

end FilteredRing_fil_map_range




section FilteredMod_fil_map_map_range

variable {R : Type u} [CommSemiring R]{ι : Type v} [OrderedCancelAddCommgroup ι]
variable (FR : ι → AddSubgroup R) [fil : FilteredRing FR]

variable {M : Type w1} [Semiring M] [Algebra R M] (FM : ι → AddSubgroup M)

variable {N : Type w2} [Semiring N] [Algebra R N]

variable [filM : FilteredModule FR FM ] (f : M →ₐ[R] N)

def filMod_map (α : ι) : AddSubgroup N := AddSubgroup.map f (FM α)

instance FilMod_map_range (f : M →ₐ[R] N) : FilteredModule FR (filMod_map FM f) where
  mono := by
    intro i j ilej y hy
    obtain ⟨x, x_in, x_eq⟩ : ∃ x ∈ FM i , f x = y := hy
    use x
    simp only [SetLike.mem_coe, (FilteredModule.mono R FR ilej) x_in, x_eq, and_self]
  smul_mem := by
    intro i j r n hr hn
    simp only [filMod_map, AddSubgroup.mem_map, vadd_eq_add] at *
    obtain ⟨x , hx, eq⟩ := hn
    rw[← eq]
    use r • x
    constructor
    · exact FilteredModule.smul_mem hr hx
    · simp only [map_smul]

end FilteredMod_fil_map_map_range




section FilteredMod_fil_map_map_range

variable {R : Type u} [CommSemiring R] {ι : Type v} [OrderedCancelAddCommgroup ι]
variable {A : Type w1} [Ring A] [Algebra R A] (𝒜 : ι → Submodule R A)
variable {B : Type w2} [Ring B] [Algebra R B]

variable [filA : FilteredAlgebra 𝒜] (f : A →ₐ[R] B)

def filAlg_map := fun (i : ι) ↦ Submodule.map f (𝒜 i)

variable (i : ι)

instance FilAlg_map_range (f : A →ₐ[R] B) : FilteredAlgebra (filAlg_map 𝒜 f) where
  mono := by
    intro i j ilej y hy
    obtain ⟨x, x_in, x_eq⟩ : ∃ x ∈ 𝒜 i , f x = y := hy
    use x
    simp only [SetLike.mem_coe, x_eq, and_true, FilteredRing.mono ilej x_in]
  one := by
    use 1
    simp only [SetLike.mem_coe, FilteredRing.one, map_one, and_self]
  mul_mem := by
    intro i j x y x_in_i y_in_j
    simp only [filAlg_map, AddSubgroup.mem_map] at *
    obtain ⟨x₁, x_in, x_eq⟩ := x_in_i
    obtain ⟨y₁, y_in, y_eq⟩ := y_in_j
    use x₁ * y₁
    simp only [SetLike.mem_coe, FilteredRing.mul_mem x_in y_in, map_mul, x_eq, y_eq, and_self]

end FilteredMod_fil_map_map_range
