import FilteredRing.Basic
import Mathlib.RingTheory.Polynomial.Basic

namespace Polynomial
variable (R : Type*) [Ring R]

instance : FilteredRing (fun i ↦ (degreeLE R i).toAddSubgroup) where
  mono {i j} hij p := by
    simp_rw [Submodule.mem_toAddSubgroup, mem_degreeLE]
    intro h
    exact h.trans hij
  one := by
    simp_rw [Submodule.mem_toAddSubgroup, mem_degreeLE]
    simp
  mul_mem {i j x y} hx hy := by
    simp_rw [Submodule.mem_toAddSubgroup, mem_degreeLE] at hx hy ⊢
    exact (degree_mul_le _ _).trans (by mono)

end Polynomial

namespace PolynomialModule
variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]

open scoped Polynomial

@[simps]
def lcoeff (n : ℕ) : (PolynomialModule R M) →ₗ[R] M where
  toFun p := p n
  map_add' p q := add_apply R p q n
  map_smul' r p := by
    dsimp
    rw [← IsScalarTower.algebraMap_smul R[X], Polynomial.algebraMap_eq,
      ← Polynomial.monomial_zero_left, monomial_smul_apply]
    simp

def degreeLE (n : WithBot ℕ) : Submodule R (PolynomialModule R M) :=
  ⨅ k : ℕ, ⨅ _ : ↑k > n, LinearMap.ker (lcoeff R M k)

def degreeLT (n : ℕ) : Submodule R (PolynomialModule R M) :=
  ⨅ k : ℕ, ⨅ (_ : k ≥ n), LinearMap.ker (lcoeff R M k)

instance : FilteredModule
    (fun i ↦ (Polynomial.degreeLE R i).toAddSubgroup)
    (fun i ↦ (degreeLE R M i).toAddSubgroup) where
  mono {i j} hij p := by
    simp? [degreeLE] says
      simp only [degreeLE, gt_iff_lt, Submodule.mem_toAddSubgroup, Submodule.mem_iInf,
        LinearMap.mem_ker, lcoeff_apply]
    intro H k hk
    exact H k (hij.trans_lt hk)
  smul_mem {i j x y} hx hy := by
    simp? [Polynomial.degreeLE, degreeLE] at hx hy ⊢ says
      simp only [Polynomial.degreeLE, gt_iff_lt, Submodule.mem_toAddSubgroup, Submodule.mem_iInf,
        LinearMap.mem_ker, Polynomial.lcoeff_apply, degreeLE, lcoeff_apply] at hx hy ⊢
    intro k hk
    rw [smul_apply]
    apply Finset.sum_eq_zero
    simp only [Finset.mem_antidiagonal, Prod.forall]
    intro ix iy hixy
    obtain (hik | hjk) : i < ix ∨ j < iy := by
      cases i with | bot => exact .inl (WithBot.bot_lt_coe _) | coe i => ?_
      cases j with | bot => exact .inr (WithBot.bot_lt_coe _) | coe j => ?_
      -- rw [← WithBot.coe_add] at hk
      erw [WithBot.coe_lt_coe] at hk
      erw [WithBot.coe_lt_coe, WithBot.coe_lt_coe]
      simp only [Nat.cast_id] at hk ⊢
      omega
    · simp [hx, hik]
    · simp [hy, hjk]

end PolynomialModule
