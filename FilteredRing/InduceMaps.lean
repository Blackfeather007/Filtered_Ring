import FilteredRing.Basic
-- import FilteredRing.test
/-!
# The filtration on abelian group and ring
In this file, we defined the fitration induced by a homomorphism,
and extend it to get the filtration on ring and module.
# Main definitions
* `SetLikeHom` This class adds the necessary conditions to describe `σA` and `σB`, ensuring that f
can induce a map from σA to σB. In this way, we can define `FB` and `FB_lt` under very weak
conditions.
* `HomtoFil` If `FA` and `FA_lt` is a filtration of A, then a map f: A → B induces a
filtration of B, which we call `FB` and `FB_lt`
* `RingHomtoFil` If `FA` and `FA_lt` is a ring filtration of A, then a ring homomorphism
 f: A →+* B induces a ring filtration of B, which we call `FB` and `FB_lt`
* `ModHomtoFil` When FM and FM_lt is a filtration of M, then a module homomorphism
 f: M → N induces a module filtration of N, which we call `FB` and `FB_lt`-/

variable {ι : Type*} [OrderedCancelAddCommMonoid ι]

section HomtoFil

variable {A : Type*} (σA : Type*) [SetLike σA A] {B : Type*} (σB : Type*) [SetLike σB B]

/-- It add some necessary conditions to describe σA and σB,ensure f can induce a map from σA → σB.-/
class SetLikeHom (f : A → B) where
  /-- It is the corresponding map from σA → σB with `coe_map` property -/
  map : σA → σB
  coe_map (x : σA) : f '' (x : Set A) = map x
  /-- `GaloisConnection` is a weakening of `LeftInverse comap map`, this design avoid adding
  `Preorder` to `σA` and `σB`, there are also theorems such as `Subgroup.gc_map_comap` to handle
  different conditions in the similar structures such as `AddSubroup`, `module`, `Ideal`. -/
  galois : ∃ comap : σB → σA, GaloisConnection map comap

open SetLikeHom Set
instance SetLikeHomInj (f : A → B)[SetLikeHom σA σB f](hf : f.Injective ):
  (map f (σA := σA) (σB := σB)).Injective := by
  intro A₁ A₂ feq
  have eq: f '' (A₁ : Set A) = f ''  (A₂ : Set A) := by
    rw[coe_map A₁ (σA := σA) (σB := σB), coe_map A₂ (σA := σA) (σB := σB)]
    exact congrArg SetLike.coe feq
  exact SetLike.coe_set_eq.mp <| (Set.image_eq_image hf).mp eq



/-- It is `F` part of the filtration induced by f: A → B -/
-- def FB (f : A → B) [SetLikeHom σA σB f] := fun (FA : ι → σA) ↦ (fun i ↦ map f (FA i) : ι → σB)
def FB (FA : ι → σA) (f : A → B) [SetLikeHom σA σB f]: ι → σB := fun i ↦ map f (FA i)

/-- It is `F_lt` part of the filtration induced by f: A → B -/
def FB_lt (FA_lt : ι → σA) (f : A → B) [SetLikeHom σA σB f] : outParam <| ι → σB :=
 fun i ↦ map f (FA_lt i)

/-- When FA and FA_lt is a filtration of A, then f: A → B induce a filtration of B which is called
`FB` and `FB_lt`-/
instance HomtoFil (FA FA_lt : ι → σA) (f : A → B) [fil : IsFiltration FA FA_lt]
[SetLikeHom σA σB f] : IsFiltration (FB σA σB FA f) (FB_lt σA σB FA_lt f) (ι := ι) where
  mono {i j i_le_j}:= by
    show (((map f <| FA i) : σB) : Set B) ≤ (((map f <| FA j) : σB) : Set B)
    rw[← coe_map <| FA i, ← coe_map <| FA j]
    exact le_iff_subset.mpr <| image_mono <| IsFiltration.mono i_le_j
  is_le {i j i_lt_j}:= by
    show (((map f <| FA i) : σB) : Set B) ≤ (((map f <| FA_lt j) : σB) : Set B)
    rw[← coe_map <| FA i, ← coe_map <| FA_lt j]
    exact le_iff_subset.mpr <| image_mono <| IsFiltration.is_le i_lt_j
  is_sup {Sup j h}:= by
    obtain⟨comap, galois⟩ := galois (f := f) (σA := σA) (σB := σB)
    apply galois.l_le
    have h : ∀ i < j, FA i ≤ comap Sup := fun i i_lt_j ↦ galois.le_u <| h i i_lt_j
    exact IsFiltration.is_sup (comap Sup) j h

-- instance (FA : ι → σA) (f : A → B) [SetLikeHom σA σB f]: IsFilteredHom FA (FB σA σB FA f) f where
--   pieces_wise := by
--     intro i a
--     simp[FB, coe_map]
--     have t1:= coe_map (FA i) (σA := σA) (σB := σB) (f := f)
--     have : f a ∈ f '' ↑(FA i) := mem_image_of_mem f <| Subtype.coe_prop a
--     rw[t1] at this
--     exact this

-- variable (i : ι) (f : A → B) [SetLikeHom σA σB f] (hf : f.Injective) (FA : ι → σA)

-- #check fun ((FA i) : σA) ↦ ((FB σA σB FA f) i : σB)

-- instance InjEletoInjEle (i : ι) (f : A → B) [SetLikeHom σA σB f] (hf : f.Injective) (FA : ι → σA):
--  Function.Injective (fun (FA i) ↦ ((FB σA σB FA f) i)) := by
-- --   intro FA₁ FA₂ feq
-- --   refine (eqOn_univ FA₁ FA₂).mp fun i _ ↦ ? i
-- --   have feq: (fun i ↦ (map f (FA₁ i) : σB)) = (fun i ↦ (map f (FA₂ i) : σB)) := feq
-- --   have : (fun i ↦ (map f (FA₁ i) : σB)) i = (fun i ↦ (map f (FA₂ i) : σB)) i := by rw[feq]
-- --   apply (SetLikeHomInj σA σB f hf) this



-- instance InjHomtoInjFil (f : A → B) [SetLikeHom σA σB f] (hf : f.Injective):
--  Function.Injective fun (FA : ι → σA) ↦ (FB σA σB FA f) := by
--   intro FA₁ FA₂ feq
--   refine (eqOn_univ FA₁ FA₂).mp fun i _ ↦ ? i
--   have feq: (fun i ↦ (map f (FA₁ i) : σB)) = (fun i ↦ (map f (FA₂ i) : σB)) := feq
--   have : (fun i ↦ (map f (FA₁ i) : σB)) i = (fun i ↦ (map f (FA₂ i) : σB)) i := by rw[feq]
--   apply (SetLikeHomInj σA σB f hf) this


-- instance SurjHomtoSurjFil (f : A → B) [SetLikeHom σA σB f] (hf : f.Surjective):
--  Function.Surjective fun (FA : ι → σA) ↦ (FB σA σB FA f) := by
--   sorry

end HomtoFil



section RingHomtoFil

variable {R : Type*} [Ring R] (σR : Type*) [SetLike σR R] [AddSubgroupClass σR R] {S : Type*}
 [Ring S] (σS : Type*) [SetLike σS S] [AddSubgroupClass σS S]

/-- It is `F` part of the ring filtration induced by f: A →+* B -/
def FS (FR : ι → σR)(f : R →+* S)[SetLikeHom σR σS f] :  ι → σS := FB σR σS FR f

/-- It is `F_lt` part of the ring filtration induced by f: A →+* B -/
def FS_lt (FR_lt : ι → σR) (f : R →+* S) [SetLikeHom σR σS f] :
outParam <| ι → σS := FB_lt σR σS FR_lt f

variable (FR : ι → σR) (FR_lt : outParam <| ι → σR) (f : R →+* S) [IsRingFiltration FR FR_lt]
[SetLikeHom σR σS f]

open SetLikeHom Set
/- When FA and FA_lt is a ring filtration of A, then ring hom f: A →+* B induce a ring filtration
 of B which is called `FB` and `FB_lt` -/
instance RingHomtoFil (FR FR_lt: ι → σR) [fil : IsRingFiltration FR FR_lt] :
    IsRingFiltration (FS σR σS FR f) (FS_lt σR σS FR_lt f) where
  __ := HomtoFil σR σS FR FR_lt f
  one_mem := by
    show 1 ∈ ((map f <| FR 0 : σS) : Set S)
    rw[← coe_map <| FR 0]
    use 1
    simp only [SetLike.mem_coe, IsRingFiltration.one_mem, map_one, and_self]
  mul_mem {i j x y x_in_i y_in_j}:= by
    show x * y ∈ ((map f <| FR <| i + j : σS) : Set S)
    rw[← coe_map <| FR <| i + j]
    have x_in_i : x ∈ ((map f (FR i) : σS) : Set S) := x_in_i
    rw[← coe_map <| FR i] at x_in_i
    have y_in_j : y ∈ ((map f (FR j) : σS) : Set S) := y_in_j
    rw[← coe_map <| FR j] at y_in_j
    obtain ⟨x₁, x_in, x_eq⟩ := x_in_i
    obtain ⟨y₁, y_in, y_eq⟩ := y_in_j
    use x₁ * y₁
    simp only [SetLike.mem_coe, IsRingFiltration.mul_mem x_in y_in, map_mul,
      Mathlib.Tactic.LinearCombination'.mul_pf x_eq y_eq, and_self]

-- instance InjtoInj2 (f : R →+* S) [SetLikeHom σR σS f] (hf : (⇑f).Injective):
--  Function.Injective fun (FR : ι → σR) ↦ (FS σR σS FR f) := InjHomtoInjFil σR σS (⇑f) hf
/- Should I leave this Thm? It is quite trivial -/

end RingHomtoFil



section ModHomtoFil

variable {R : Type*} [Ring R] (σR : Type*) [SetLike σR R] [AddSubgroupClass σR R]
variable (FR : ι → σR) (FR_lt : outParam <| ι → σR) [fil : IsRingFiltration FR FR_lt]

variable {M : Type*} [AddCommMonoid M] [Module R M] (σM : Type*) [SetLike σM M]
[AddSubmonoidClass σM M] [SMulMemClass σM R M] (FM : ι → σM) (FM_lt : outParam <| ι → σM)

variable {N : Type*} [AddCommMonoid N] [Module R N] (σN : Type*) [SetLike σN N]
[AddSubmonoidClass σN N] [SMulMemClass σN R N]

variable [filM : IsModuleFiltration FR FR_lt FM FM_lt] (f : M →ₗ[R] N)

/-- It is `F'` part of the module filtration induced by f: A →+* B -/
def FN (FM : ι → σM) (f : M →ₗ[R] N) [SetLikeHom σM σN f] : ι → σN := FB σM σN FM f

/-- It is `F'_lt` part of the module filtration induced by f: A →+* B -/
def FN_lt (FM_lt : ι → σM) (f : M →ₗ[R] N) [SetLikeHom σM σN f] : outParam <| ι → σN :=
 FB_lt σM σN FM_lt f

/- When FM and FM_lt is a filtration of M, then module hom f: M → N induce a module filtration of B
 which is called `FB` and `FB_lt`-/
open SetLikeHom
instance ModHomtoFil [SetLikeHom σM σN f] :
    IsModuleFiltration FR FR_lt (FN σM σN FM f) (FN_lt σM σN FM_lt f) where
  __ := HomtoFil σM σN (f := f.toFun) (ι := ι) (FA := FM) (FA_lt := FM_lt)
  smul_mem {i j r n hr hn}:= by
    have hn : n ∈ ((map f <| FM j : σN) : Set N) := hn
    rw[← coe_map <| FM j] at hn
    obtain⟨m, hm, heq⟩ := hn
    show r • n ∈ ((map f (FM <| i + j) : σN) : Set N)
    rw[← coe_map <| FM (i + j), ← heq, ← (LinearMap.CompatibleSMul.map_smul f r m)]
    use r • m
    have := IsModuleFiltration.smul_mem hr hm
    rw[vadd_eq_add] at this
    simp only [SetLike.mem_coe, this, map_smul, and_self]

end ModHomtoFil
