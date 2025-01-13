import Mathlib

universe u v w

variable {ι : Type v} [OrderedAddCommMonoid ι]

variable {A : Type u} [AddCommMonoid A] {σ : Type*} [SetLike σ A] [AddSubmonoidClass σ A]

class IsFiltration (F : ι → σ) (F_lt : outParam <| ι → σ) : Prop where
  mono {i j} : i ≤ j → F i ≤ F j
  is_le {i} : i < j → F i ≤ F_lt j
  is_sup (B : σ) (j : ι) : (∀ i < j, F i ≤ B) → F_lt j ≤ B
-- F_lt j = ⨆ i < j, F i

--for integer
instance (F : ℤ → σ) (mono : ∀ {a b : ℤ}, a ≤ b → F a ≤ F b) : IsFiltration F (fun n ↦ F (n - 1)) where
  mono := mono
  is_le lt := mono (Int.le_sub_one_of_lt lt)
  is_sup _ j hi := hi (j - 1) (sub_one_lt j)

class IsExhaustiveFiltration (F : ι → σ) (F_lt : ι → σ) [IsFiltration F F_lt] : Prop where
  exhaustive : A = ⋃ i, (F i : Set A)

class IsDiscreteFiltration (F : ι → σ) (F_lt : ι → σ) [IsFiltration F F_lt] : Prop where
  discrete : ∃ n : ι, ∀ i ≤ n,
    Set.range (AddSubmonoidClass.subtype (F i)) = (⊥ : AddSubmonoid A)


section FilteredRing

variable {R : Type u} [Semiring R] {σ : Type*} [SetLike σ R] [AddSubmonoidClass σ R]

class IsRingFiltration (F : ι → σ) (F_lt : outParam <| ι → σ) extends IsFiltration F F_lt : Prop where
  one_mem : 1 ∈ F 0
  mul_mem : ∀ {i j x y}, x ∈ F i → y ∈ F j → x * y ∈ F (i + j)

instance (F : ι → σ) (F_lt : outParam <| ι → σ) [IsRingFiltration F F_lt] : Semiring (F 0) := {
  mul := fun x y ↦ ⟨x.1 * y.1, by simpa using IsRingFiltration.mul_mem x.2 y.2⟩
  left_distrib := fun a b c ↦ SetCoe.ext (mul_add a.1 b.1 c.1)
  right_distrib := fun a b c ↦ SetCoe.ext (add_mul a.1 b.1 c.1)
  zero_mul := fun a ↦ SetCoe.ext (zero_mul a.1)
  mul_zero := fun a ↦ SetCoe.ext (mul_zero a.1)
  mul_assoc := fun a b c ↦ SetCoe.ext (mul_assoc a.1 b.1 c.1)
  one := ⟨1, IsRingFiltration.one_mem⟩
  one_mul := fun a ↦ SetCoe.ext (one_mul a.1)
  mul_one := fun a ↦ SetCoe.ext (mul_one a.1) }

--for integer
instance (F : ℤ → σ) (mono : ∀ {a b : ℤ}, a ≤ b → F a ≤ F b) (one_mem : 1 ∈ F 0)
  (mul_mem : ∀ {i j x y}, x ∈ F i → y ∈ F j → x * y ∈ F (i + j)) : IsRingFiltration F (fun n ↦ F (n - 1)) := {
    instIsFiltrationIntHSubOfNat F mono with
    one_mem := one_mem
    mul_mem := mul_mem }

end FilteredRing


section FilteredModule

variable {R : Type u} [Semiring R] {σ : Type*} [SetLike σ R] [AddSubmonoidClass σ R]

variable {M : Type*} {ιM : Type*} [OrderedAddCommMonoid ιM] [VAdd ι ιM] {σM : Type*} [SetLike σM M]
--`ιM` can be more general, however usually we take `ιM = ι`

variable [AddCommMonoid M] [AddSubmonoidClass σM M] in
class IsModuleFiltration [Module R M] (F : ι → σ) (F_lt : outParam <| ι → σ) [IsRingFiltration F F_lt]
    (F' : ιM → σM) (F'_lt : ιM → σM) extends IsFiltration F' F'_lt : Prop where
  smul_mem : ∀ {i j x y}, x ∈ F i → y ∈ F' j → x • y ∈ F' (i +ᵥ j)

end FilteredModule


section FilteredAlgebra

variable {R : Type u} [CommSemiring R] {𝒜 : Type w} [Semiring 𝒜] [Algebra R 𝒜]

variable {σ : Type*} [SetLike σ 𝒜] [AddSubmonoidClass σ 𝒜] [SMulMemClass σ R 𝒜]

abbrev IsAlgebraFiltration (F : ι → σ) (F_lt : outParam <| ι → σ) := IsRingFiltration F F_lt

end FilteredAlgebra
