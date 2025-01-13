import FilteredRing.Basic

section FilteredRing_fil_map_range

variable {ι : Type v} [OrderedCancelAddCommMonoid ι]
{R : Type*} [Ring R] (σR : Type*) [SetLike σR R] [AddSubgroupClass σR R]
{S : Type*} [Ring S] (σS : Type*) [SetLike σS S] [AddSubgroupClass σS S]

class SubgroupClassHom (f : R →+* S) where
  map : σR → σS
  image_coe_eq_coe_map (x : σR) : f '' (x : Set R) = map x

def FS (FR : ι → σR)(f : R →+* S)[SubgroupClassHom σR σS f] : ι → σS :=
  fun i ↦ SubgroupClassHom.map f (FR i)

def FS_lt (FR_lt : ι → σR) (f : R →+* S) [SubgroupClassHom σR σS f] :  outParam <| ι → σS :=
  fun i ↦ SubgroupClassHom.map f (FR_lt i)

class SubgroupClasscomap (f : R →+* S) where
  comap (y : σS) : σR
  property (y : σS) : (comap y : Set R) = ⇑f ⁻¹' y

variable (FR : ι → σR) (FR_lt : outParam <| ι → σR) (f : R →+* S)
  [SubgroupClassHom σR σS f]

open SubgroupClassHom Set


private lemma ele_map_to_image [SubgroupClasscomap σR σS f] {A: σR}{x : S} :
    x ∈ ⇑f '' (A : Set R) → x ∈ (map f <| A : σS):= by
  show x ∈ ⇑f '' (A : Set R) → x ∈ (((map f <| A) : σS) : Set S)
  simp only[← image_coe_eq_coe_map <| A, imp_self]

private lemma map_to_image [SubgroupClasscomap σR σS f] {A B: σR} :
    ⇑f '' (A : Set R) ≤ ⇑f '' (B : Set R) → (map f <| A : σS) ≤ (map f <| B : σS):= by
  show ⇑f '' (A : Set R) ≤ ⇑f '' (B : Set R) → (((map f <| A) : σS) : Set S) ≤ (((map f <| B) : σS) : Set S)
  simp only [image_subset_iff, ← image_coe_eq_coe_map <| A, ← image_coe_eq_coe_map <| B, imp_self]



instance Filtered_fil_map_range [fil : IsFiltration FR FR_lt]
[SubgroupClasscomap σR σS f] : IsFiltration (FS σR σS FR f) (FS_lt σR σS FR_lt f) where
  mono := by
    intro i j i_le_j
    apply map_to_image
    exact le_iff_subset.mpr <| image_mono <| IsFiltration.mono i_le_j
  is_le := by
    intro j i i_lt_j
    apply map_to_image
    exact le_iff_subset.mpr <| image_mono <| IsFiltration.is_le i_lt_j
  is_sup := by
    intro B j h
    show ((map f (FR_lt j) : σS): Set S) ≤ (B : Set S)
    rw[← image_coe_eq_coe_map <| FR_lt j]

    refine le_iff_subset.mpr <| image_subset_iff.mpr ?_

    have h : ∀ i < j, ↑(FR i) ≤ ⇑f ⁻¹' ↑B := by
      intro i i_lt_j
      have : (⇑f '' (FR i) : Set S) ≤ B := by
        have : ((map f (FR i) : σS) : Set S) ≤ (B : Set S) := h i i_lt_j
        rw[← image_coe_eq_coe_map <| FR i] at this
        exact this
      exact le_iff_subset.mpr <| image_subset_iff.mp this

    have : (SubgroupClasscomap.comap f B : σR) = ⇑f ⁻¹' B := SubgroupClasscomap.property B
    rw[← this] at h ⊢
    exact IsFiltration.is_sup (SubgroupClasscomap.comap f B : σR) j h

instance [fil : IsRingFiltration FR FR_lt] [SubgroupClasscomap σR σS f] :
  IsRingFiltration (FS σR σS FR f) (FS_lt σR σS FR_lt f) where
    __ := Filtered_fil_map_range σR σS FR FR_lt f
    one_mem := by
      apply ele_map_to_image
      use 1
      simp only [SetLike.mem_coe, IsRingFiltration.one_mem, map_one, and_self]
    mul_mem := by
      intro i j x y x_in_i y_in_j

      apply ele_map_to_image

      have x_in_i : x ∈ ((map f (FR i) : σS) : Set S) := x_in_i
      rw[← image_coe_eq_coe_map <| FR i] at x_in_i

      have y_in_j : y ∈ ((map f (FR j) : σS) : Set S) := y_in_j
      rw[← image_coe_eq_coe_map <| FR j] at y_in_j

      obtain ⟨x₁, x_in, x_eq⟩ := x_in_i
      obtain ⟨y₁, y_in, y_eq⟩ := y_in_j
      use x₁ * y₁
      simp only [SetLike.mem_coe, IsRingFiltration.mul_mem x_in y_in, map_mul,
        Mathlib.Tactic.LinearCombination'.mul_pf x_eq y_eq, and_self]


end FilteredRing_fil_map_range

/-


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

end FilteredMod_fil_map_map_range-/
