/-
Copyright (c) 2025 Huanyu Zheng, Weichen Jiao, Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
import FilteredRing.Exactness
import Mathlib.Tactic.Linarith.Frontend

variable {R S T σR σS σT : Type*}

variable [Ring R] [SetLike σR R] [AddSubgroupClass σR R]

variable [Ring S] [SetLike σS S] [AddSubgroupClass σS S]

variable [Ring T] [SetLike σT T] [AddSubgroupClass σT T]

variable {FR : ℤ → σR} {FS : ℤ → σS} {FT : ℤ → σT}

variable [IsRingFiltration FS (fun n ↦ FS (n - 1))] [IsRingFiltration FT (fun n ↦ FT (n - 1))]

variable (f : FilteredRingHom FR (fun n ↦ FR (n - 1)) FS (fun n ↦ FS (n - 1)))
variable (g : FilteredRingHom FS (fun n ↦ FS (n - 1)) FT (fun n ↦ FT (n - 1)))
variable [hasGMul FR fun n ↦ FR (n - 1)] [hasGMul FT fun n ↦ FT (n - 1)]
  [hasGMul FS fun n ↦ FS (n - 1)]

open RingHom DirectSum DFinsupp FilteredRingHom FilteredAddGroupHom GradedPiece


theorem exists_nonneg_x_in_filtration (x : S) (p : ℤ)
(Exhaustive : IsExhaustiveFiltration FS (fun n ↦ FS (n - 1)))
 : ∃ s, s ≥ 0 ∧ (x : S) ∈ FS (p + s) := by
  obtain ⟨s₀, xin⟩ : ∃ s, (x : S) ∈ FS s := by
    apply Set.mem_iUnion.mp
    rw[IsExhaustiveFiltration.exhaustive (fun n ↦ FS (n - 1)) (F := FS) (A := S)]
    trivial
  rcases lt_or_le p s₀ with ch | ch
  · exact ⟨s₀ - p, by simp only [ge_iff_le, sub_nonneg, add_sub_cancel, xin, and_true, le_of_lt ch]⟩
  · exact ⟨0, by simp only [ge_iff_le, le_refl, add_zero, (IsFiltration.mono ch) xin, and_self]⟩




#check Int.le_induction_down
#check Nat.decreasingInduction'
--**It needs refactor**
lemma Int.decreasingInduction' (m n : ℤ) {P : ℤ → Prop}
    (h : (k : ℤ) → k ≤ n → m < k → P k → P (k - 1)) (mn : m ≤ n) (hP : P n) : P m := by
  have (s : ℕ) (hs : s < n - m) : P (n - s) → P (n - s - 1) :=
    h (n - s) (by linarith) (by linarith[hs])
  obtain⟨r, hr⟩ : ∃ r : ℕ, r = n - m := CanLift.prf (n - m) (by linarith)
  have : m = n - r := by simp only [hr, sub_sub_cancel]
  rw[this]
  have (t : ℕ) (hs : t ≤ n - m) : P (n - t) := by
    induction' t with t ih
    · simp[hP]
    · have : n - (t : ℤ) - 1 = n - ((t + 1 : ℕ) : ℤ) := Int.sub_sub n (↑t) 1
      rw[← this]
      apply h (n - t) (by linarith) (by linarith[hs])
      apply ih (by linarith[hs])
  apply this
  simp only [hr, le_refl]



omit [IsRingFiltration FS fun n ↦ FS <| n - 1] [IsRingFiltration FT fun n ↦ FT <| n - 1] in
lemma Ggker_eq_Gfrange (Gexact : Function.Exact Gr[f] Gr[g]) (i : ℤ) :
    Gr(i)[g].ker = Set.range Gr(i)[f] := by
  ext u

  sorry
  /-apply Iff.trans (Gf_zero_iff_of_in_ker g u) ?_
  have := (Gf_in_range_iff_of_in_range f u).symm
  exact Iff.trans (Gexact ((of (GradedPiece FS fun n ↦ FS (n - 1)) i) u)) this-/


lemma induction_lemma (p s k: ℤ) (k_le : k ≤ p + s) (lt_k : p < k) (x : S) (xin : x ∈ FS k)
    (fg_exact : Function.Exact f.toRingHom g.toRingHom) (GfGg_exact : Function.Exact Gr[f] Gr[g]) :
    g.toRingHom x ∈ g.toRingHom '' (FS (k - 1)) := by
  obtain⟨z₀, hz₀⟩ : ⟦⟨x, xin⟩⟧ ∈ Set.range Gr(k)[f] := by
    rw[← Ggker_eq_Gfrange f g GfGg_exact k]
    show Gr(k)[g] (mk FS (fun n ↦ FS (n - 1)) ⟨x, xin⟩) = 0
    simp [GradedPieceHom_apply_mk_eq_mk_piece_wise_hom g ⟨x, xin⟩, eq_zero_iff]
    show (g.toRingHom x) ∈ FT (k - 1)





    sorry
    -- refine Gf_zero g hx klt hy1
  obtain⟨z, hz⟩ : ∃ z , Gr(k)[f] ⟦z⟧ = ⟦⟨x, xin⟩⟧ := by
    obtain⟨z, eq⟩ := Quotient.exists_rep z₀
    exact ⟨z, by rw[eq, hz₀]⟩
  obtain⟨x', hx'⟩ : ∃ x' ∈ FS (k - 1), g.toRingHom x = g.toRingHom x' := by
    use x - f.toRingHom ↑z
    sorry
  sorry


lemma induction_lemma1 (p s : ℤ) (x : S)
    (fg_exact : Function.Exact f.toRingHom g.toRingHom) (GfGg_exact : Function.Exact Gr[f] Gr[g]) :
    ∀ k ≤ p + s, p < k → g.toRingHom x ∈ g.toRingHom '' (FS k) →
    g.toRingHom x ∈ g.toRingHom '' (FS (k - 1)) := sorry



theorem strictness_under_exact_and_exhaustive'
    (fg_exact : Function.Exact f.toRingHom g.toRingHom) (GfGg_exact : Function.Exact Gr[f] Gr[g])
    (Exhaustive : IsExhaustiveFiltration FS (fun n ↦ FS (n - 1))) (p : ℤ) (y : T) :
 y ∈ FT p → y ∈ Set.range g.toRingHom → y ∈ g.toRingHom '' (FS p : Set S) := by
  intro yinFT ⟨x, hx⟩
  rw[← hx]
  obtain⟨s, sge0, xin⟩ : ∃s, s ≥ 0 ∧ x ∈ FS (p + s) := exists_nonneg_x_in_filtration x p Exhaustive
  rcases Or.symm (LE.le.gt_or_eq sge0) with ch | ch
  · rw[ch, add_zero] at xin
    exact Set.mem_image_of_mem (⇑g.toRingHom) xin
  · apply Int.decreasingInduction' (P := fun n ↦ g.toRingHom x ∈ g.toRingHom '' (FS n)) (n := p + s)
    · sorry
    · linarith
    · exact Set.mem_image_of_mem (⇑g.toRingHom) xin



theorem strictness_under_exact_and_exhaustive
    (fg_exact : Function.Exact f.toRingHom g.toRingHom) (GfGg_exact : Function.Exact Gr[f] Gr[g])
    (Exhaustive : IsExhaustiveFiltration FS (fun n ↦ FS (n - 1))) : g.IsStrict := by
  constructor
  · intro p y
    exact strictness_under_exact_and_exhaustive' f g fg_exact GfGg_exact Exhaustive p y
  · intro p y
    exact strictness_under_exact_and_exhaustive' f g fg_exact GfGg_exact Exhaustive (p - 1) y
