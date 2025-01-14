import FilteredRing.Basic


variable {ι : Type v} [OrderedCancelAddCommMonoid ι]

section HomtoFiltration

variable {A : Type*} [AddCommMonoid A] (σA : Type*) [SetLike σA A] [AddSubmonoidClass σA A]
{B : Type*} [AddCommMonoid B] (σB : Type*) [SetLike σB B] [AddSubmonoidClass σB B]

class SubmonoidClassHom (f : A → B) where
  map : σA → σB
  image_coe_eq_coe_map (x : σA) : f '' (x : Set A) = map x

def FB (FA : ι → σA)(f : A → B)[SubmonoidClassHom σA σB f] : ι → σB :=
  fun i ↦ SubmonoidClassHom.map f (FA i)

def FB_lt (FA_lt : ι → σA) (f : A → B) [SubmonoidClassHom σA σB f] :  outParam <| ι → σB :=
  fun i ↦ SubmonoidClassHom.map f (FA_lt i)

class SubmonoidClasscomap (f : A → B) where
  comap (y : σB) : σA
  property (y : σB) : (comap y : Set A) = f ⁻¹' y


open SubmonoidClassHom Set
instance HomtoFiltration [fil : IsFiltration FA FA_lt] [SubmonoidClassHom σA σB f]
[SubmonoidClasscomap σA σB f] : IsFiltration (FB σA σB FA f) (FB_lt σA σB FA_lt f) (ι := ι) where
  mono := by
    intro i j i_le_j
    show (((map f <| FA i) : σB) : Set B) ≤ (((map f <| FA j) : σB) : Set B)
    rw[← image_coe_eq_coe_map <| FA i, ← image_coe_eq_coe_map <| FA j]
    exact le_iff_subset.mpr <| image_mono <| IsFiltration.mono i_le_j
  is_le := by
    intro j i i_lt_j
    show (((map f <| FA i) : σB) : Set B) ≤ (((map f <| FA_lt j) : σB) : Set B)
    rw[← image_coe_eq_coe_map <| FA i, ← image_coe_eq_coe_map <| FA_lt j]
    exact le_iff_subset.mpr <| image_mono <| IsFiltration.is_le i_lt_j
  is_sup := by
    intro Sup j h
    show ((map f (FA_lt j) : σB): Set B) ≤ (Sup : Set B)
    rw[← image_coe_eq_coe_map <| FA_lt j]

    refine le_iff_subset.mpr <| image_subset_iff.mpr ?_

    have h : ∀ i < j, ↑(FA i) ≤ f ⁻¹' ↑Sup := by
      intro i i_lt_j
      have : (f '' (FA i) : Set B) ≤ Sup := by
        have : ((map f (FA i) : σB) : Set B) ≤ (Sup : Set B) := h i i_lt_j
        rw[← image_coe_eq_coe_map <| FA i] at this
        exact this
      exact le_iff_subset.mpr <| image_subset_iff.mp this

    have : (SubmonoidClasscomap.comap f Sup : σA) = f ⁻¹' Sup := SubmonoidClasscomap.property Sup
    rw[← this] at h ⊢
    exact IsFiltration.is_sup (SubmonoidClasscomap.comap f Sup : σA) j h

end HomtoFiltration




section RingHomtoFiltration

variable {R : Type*} [Ring R] (σR : Type*) [SetLike σR R] [AddSubgroupClass σR R]
{S : Type*} [Ring S] (σS : Type*) [SetLike σS S] [AddSubgroupClass σS S]


def FS (FR : ι → σR)(f : R →+* S)[SubmonoidClassHom σR σS f][SubmonoidClassHom σR σS f] :
 ι → σS := FB σR σS FR f

def FS_lt (FR_lt : ι → σR) (f : R →+* S) [SubmonoidClassHom σR σS f] [SubmonoidClassHom σR σS f]:
 outParam <| ι → σS := FB_lt σR σS FR_lt f

variable (FR : ι → σR) (FR_lt :  outParam <| ι → σR) (f : R →+* S) [fil : IsRingFiltration FR FR_lt]
[SubmonoidClassHom σR σS f]

open SubmonoidClassHom Set

instance ele_map_to_image [SubmonoidClasscomap σR σS f] {A: σR}{x : S} :
    x ∈ ⇑f '' (A : Set R) → x ∈ (map f <| A : σS):= by
  show x ∈ ⇑f '' (A : Set R) → x ∈ (((map f <| A) : σS) : Set S)
  simp only[← image_coe_eq_coe_map <| A, imp_self]

instance RingHomtoFiltration [fil : IsRingFiltration FR FR_lt] [SubmonoidClasscomap σR σS f] :
  IsRingFiltration (FS σR σS FR f) (FS_lt σR σS FR_lt f) where
    __ := HomtoFiltration σR σS
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

end RingHomtoFiltration





section ModuleHomtoFiltration

variable {R : Type*} [Ring R] (σR : Type*) [SetLike σR R] [AddSubgroupClass σR R]
variable (FR : ι → σR) (FR_lt : outParam <| ι → σR) [fil : IsRingFiltration FR FR_lt]

variable {M : Type*} [AddCommMonoid M] [Module R M] (σM : Type*) [SetLike σM M]
[AddSubmonoidClass σM M] [SMulMemClass σM R M] (FM : ι → σM) (FM_lt : outParam <| ι → σM)

variable {N : Type*} [AddCommMonoid N] [Module R N] (σN : Type*) [SetLike σN N]
[AddSubmonoidClass σN N] [SMulMemClass σN R N]

variable [filM : IsModuleFiltration FR FR_lt FM FM_lt] (f : M →ₗ[R] N)

def FN (FM : ι → σM) (f : M →ₗ[R] N)[SubmonoidClassHom σM σN f] [SubmonoidClassHom σM σN f]
: ι → σN := FB σM σN FM f

def FN_lt (FM_lt : ι → σM) (f : M →ₗ[R] N) [SubmonoidClassHom σM σN f] [SubmonoidClassHom σM σN f]
: outParam <| ι → σN := FB_lt σM σN FM_lt f

open SubmonoidClassHom
instance ModuleHomtoFiltration [SubmonoidClassHom σM σN f] [SubmonoidClasscomap σM σN f.toFun] :
    IsModuleFiltration FR FR_lt (FN σM σN FM f) (FN_lt σM σN FM_lt f) where
  __ := HomtoFiltration σM σN (f := f.toFun) (ι := ι) (FA := FM) (FA_lt := FM_lt)
  smul_mem := by
    intro i j r n hr hn
    have hn : n ∈ ((map f <| FM j : σN) : Set N) := hn
    rw[← image_coe_eq_coe_map <| FM j] at hn
    obtain⟨m, hm, heq⟩ := hn

    show r • n ∈ ((map f (FM <| i + j) : σN) : Set N)
    rw[← image_coe_eq_coe_map <| FM (i + j), ← heq, ← (LinearMap.CompatibleSMul.map_smul f r m)]
    use r • m

    have := IsModuleFiltration.smul_mem hr hm
    rw[vadd_eq_add] at this
    simp only [SetLike.mem_coe, this, map_smul, and_self]

end ModuleHomtoFiltration





section AlgebraHomtoFiltration

variable {R : Type*} [CommSemiring R]
{𝒜 : Type*}[Ring 𝒜][Algebra R 𝒜]{σA : Type*}[SetLike σA 𝒜][AddSubmonoidClass σA 𝒜][SMulMemClass σA R 𝒜]
(FA : ι → σA)(FA_lt : outParam <| ι → σA)
{ℬ : Type*}[Ring ℬ][Algebra R ℬ]{σB : Type*}[SetLike σB ℬ][AddSubmonoidClass σB ℬ][SMulMemClass σB R ℬ]
(f : 𝒜 →ₐ[R] ℬ)

theorem AlgebraHomtoFiltration [SubmonoidClassHom σA σB f] [SubmonoidClasscomap σA σB f.toFun] [IsAlgebraFiltration FA FA_lt]:
    IsAlgebraFiltration (FB σA σB FA f.toFun) (FB_lt σA σB FA_lt f.toFun) where
  __ := RingHomtoFiltration σA σB FA FA_lt f.toRingHom

end AlgebraHomtoFiltration
