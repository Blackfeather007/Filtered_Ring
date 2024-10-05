import Mathlib

universe u v w

open scoped DirectSum

open SuccOrder

section filtered_group

variable (G : Type u) [Group G] (ι : Type v) [OrderedAddCommMonoid ι] [SuccOrder ι] [DecidableEq ι]

/- ascending filtration -/
structure Group.Filtration where
  fil : ι → Subgroup G
  normal : ∀ i : ι, (fil i).Normal
  mono : ∀ i : ι, fil i ≤ fil (succ i)
  one : 1 ∈ fil 0

class FilteredGroup extends Group.Filtration G ι

variable (G : Type u) [AddGroup G] (ι : Type v) [OrderedAddCommMonoid ι] [SuccOrder ι] [DecidableEq ι]

structure AddGroup.Filtration where
  fil : ι → AddSubgroup G
  normal : ∀ i : ι, (fil i).Normal
  mono : ∀ i : ι, fil i ≤ fil (succ i)
  one : 0 ∈ fil 0

class FilteredAddGroup extends AddGroup.Filtration G ι

end filtered_group


section filtered_ring

variable (R : Type u) (ι : Type v) [Ring R] [OrderedAddCommMonoid ι] [SuccOrder ι] [DecidableEq ι]

structure Ring.Filtration extends AddGroup.Filtration R ι

/- definition of Filtered Ring -/
class FilteredRing extends Ring.Filtration R ι

open Polynomial
-- /- definition of Filtered Module -/
-- variable {A : Type w} [Ring A] [Module R A]
-- class FilteredModule (𝓐 : ι → Submodule R A) where
--   whole : iSup 𝓐 = ⊤
--   mono : Monotone 𝓐
--   -- smul_le : ∀ i j, (𝓐 i : ) • 𝓐 j ≤ 𝓐 (i + j)
--   one : 1 ∈ 𝓐 0

-- variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)
-- variable {N : Submodule R M}
-- #synth SMul (Ideal R) (Submodule R M)
-- #check I • N
-- structure Module.Filtration (M : Type u) [AddCommGroup M] [Module R M] where
--   F : ℕ → Submodule R M
--   mono : ∀ i, F (i + 1) ≤ F i
--   smul_le : ∀ i, I • F i  ≤ F (i + 1)
-- -- need R to be a commRing

end filtered_ring

section Example

variable {R : Type u} {ι : Type v} [Ring R]

variable (ι : Type v) [OrderedAddCommMonoid ι] [SuccOrder ι] [DecidableEq ι] in
def trivialFiltration : Ring.Filtration R ι where
  fil := sorry
  normal := sorry
  mono := sorry
  one := sorry

variable (I : Ideal R) in
/- I-adic Filtration -/
def I_adic_Filtration : Ring.Filtration R ℤ where
  fil := sorry
  normal := sorry
  mono := sorry
  one := sorry

end Example


section CategoryTheory



end CategoryTheory

-- variable {R : Type u} {A : Type v} {ι : Type w}
-- [CommRing R] [Ring A] [Algebra R A] [OrderedAddCommMonoid ι] [PredOrder ι] [DecidableEq ι]

-- class FilteredAlgebra (𝓐 : ι → Submodule R A) where
--   whole : iSup 𝓐 = ⊤
--   mono : Monotone 𝓐
--   mul_compat : ∀ i j, 𝓐 i * 𝓐 j ≤ 𝓐 (i + j)
--   one : 1 ∈ 𝓐 0

-- namespace FilteredAlgebra

-- def aux (𝓐 : ι → Submodule R A) (i : ι) [FilteredAlgebra 𝓐] : Submodule R A :=
--   match decEq i (Order.pred i) with
--   | isTrue _ => ⊥
--   | isFalse _ => 𝓐 (Order.pred i)

-- def gradedObject (𝓐 : ι → Submodule R A) (i : ι) [FilteredAlgebra 𝓐] :=
--   Submodule.map (aux 𝓐 i).mkQ <| 𝓐 i
