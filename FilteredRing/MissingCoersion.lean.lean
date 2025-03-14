/-
Copyright (c) 2025 Huanyu Zheng, Weichen Jiao, Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Huanyu Zheng, Weichen Jiao, Yi Yuan
-/
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Ring.Subring.Basic

open DirectSum
section

variable {ι : Type*} {α : ι → Type*} {β : ι → Type*} [∀ i, AddCommGroup (α i)]
variable [∀ i, AddCommGroup (β i)] (f : ∀(i : ι), α i →+ β i)

lemma mem_map_ker_iff (x : ⨁ i, α i) : x ∈ (map f).ker ↔ ∀ i, x i ∈ (f i).ker := by
  refine ⟨fun h i ↦ ?_, fun h ↦ ?_⟩
  · rw [AddMonoidHom.mem_ker, ← map_apply, h, zero_apply]
  · ext i
    exact h i

lemma of_mem_map_ker_iff [DecidableEq ι] (i : ι) (x : α i) :
    (of α i x) ∈ (map f).ker ↔ x ∈ (f i).ker := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp only [AddMonoidHom.mem_ker, map_of] at h
    exact DFinsupp.single_eq_zero.mp h
  · simp [AddMonoidHom.mem_ker.mp h]

lemma mem_map_range_iff (y : ⨁ i, β i) [DecidableEq ι] [(i : ι) → (x : β i) → Decidable (x ≠ 0)] :
    y ∈ (map f).range ↔ ∀ i, y i ∈ (f i).range := by
  refine ⟨fun ⟨x, hx⟩ i ↦ ?_, fun h ↦ ?_⟩
  · simp [← hx]
  · use DirectSum.mk α y.support (fun i ↦ Classical.choose (h i))
    ext i
    simp only [Finset.coe_sort_coe, map_apply]
    by_cases mem : i ∈ y.support
    · rw [← Classical.choose_spec (h i)]
      exact congrArg (f i) (mk_apply_of_mem mem)
    · rw [DFinsupp.not_mem_support_iff.mp mem, ← map_zero (f i)]
      exact congrArg (f i) (mk_apply_of_not_mem mem)

lemma of_mem_map_range_iff (i : ι) (y : β i) [DecidableEq ι] :
    (of β i y) ∈ (map f).range ↔ y ∈ (f i).range := by
  refine ⟨fun ⟨x, hx⟩ ↦ ?_, fun ⟨x, hx⟩ ↦ ?_⟩
  · use x i
    rw [← of_eq_same i y, ← hx, map_apply]
  · use of α i x
    simp [hx]

end
