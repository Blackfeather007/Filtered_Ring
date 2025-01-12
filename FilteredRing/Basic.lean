import Mathlib

universe u v w

variable {ι : Type v} [OrderedAddCommMonoid ι]

variable {A : Type u} [AddCommMonoid A] {σ : Type*} [SetLike σ A] [AddSubmonoidClass σ A]

class IsFiltration (F : ι → σ) (F_lt : ι → σ) : Prop where
  mono {i j} : i ≤ j → F i ≤ F j
  is_le : ∀ i < j, F i ≤ F_lt j
  is_sup (B : σ) (j : ι) : (∀ i < j, F i ≤ B) → F_lt j ≤ B

variable {R : Type u} [Semiring R] {σ : Type*} [SetLike σ R] [AddSubmonoidClass σ R]

class IsRingFiltration (F : ι → σ) (F_lt : outParam <| ι → σ) extends IsFiltration F F_lt : Prop where
  one_mem : 1 ∈ F 0
  mul_mem : ∀ {i j x y}, x ∈ F i → y ∈ F j → x * y ∈ F (i + j)

variable {M : Type*}
variable {ιM : Type*} [OrderedAddCommMonoid ιM] [VAdd ι ιM]
variable {σM : Type*} [SetLike σM M]
--`ιM` can be more general, however usually we take `ιM = ι`

variable [AddCommMonoid M] [AddSubmonoidClass σM M] in
class IsModuleFiltration [Module R M] (F : ι → σ) (F_lt : ι → σ) [IsRingFiltration F F_lt]
    (F' : ιM → σM) (F'_lt : ιM → σM) extends IsFiltration F' F'_lt : Prop where
  smul_mem : ∀ {i j x y}, x ∈ F i → y ∈ F' j → x • y ∈ F' (i +ᵥ j)
