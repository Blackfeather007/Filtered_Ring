import FilteredRing.Basic

universe u v w

suppress_compilation


variable {R : Type u} {ι : Type v} [OrderedCancelAddCommMonoid ι] [DecidableEq ι]

section

variable [Ring R]

def F_le (F : ι → AddSubgroup R) : ι → AddSubgroup R := fun i ↦ ⨆ k ≤ i, F k

def F_lt (F : ι → AddSubgroup R) : ι → AddSubgroup R := fun i ↦ ⨆ k < i, F k

instance Graded_to_Filtered (F : ι → AddSubgroup R) [GradedRing F] :
  IsFiltration (F_le F) (F_lt F) where
    mono := by
      intro i j h
      have : ∀ k ≤ i, F k ≤ ⨆ k, ⨆ (_ : k ≤ j), F k :=
        fun k hk ↦ le_biSup F (Preorder.le_trans k i j hk h)
      exact iSup_le (fun k ↦ iSup_le (fun t ↦ this k t))
    is_le := by
      intro j i i_lt_j
      apply iSup_mono'
      intro k; use k
      simp only [iSup_le_iff]
      intro k_le_i
      apply le_iSup_iff.mpr
      exact fun _ hb ↦ hb (lt_of_le_of_lt k_le_i i_lt_j)
    is_sup := by
      intro b j h
      simp[F_lt, F_le] at *
      intro k k_lt_j
      apply h k k_lt_j k (Preorder.le_refl k)



instance Graded_to_FilteredRing (F : ι → AddSubgroup R) [GradedRing F] :
  IsRingFiltration (F_le F) (F_lt F) where
    __ := Graded_to_Filtered F
    one_mem :=
      have : F 0 ≤ ⨆ k, ⨆ (_ : k ≤ 0), F k := (le_biSup F (Preorder.le_refl 0))
      this SetLike.GradedOne.one_mem
    mul_mem := by
      intro i j x y hx hy
      let S : AddSubgroup R := {
        carrier := {z | z * y ∈ F_le F (i + j)}
        add_mem' := fun ha hb ↦ by simp only [Set.mem_setOf_eq, add_mul, add_mem ha.out hb.out]
        zero_mem' := by simp only [Set.mem_setOf_eq, zero_mul, zero_mem]
        neg_mem' := by simp only [Set.mem_setOf_eq, neg_mul, neg_mem_iff, imp_self, implies_true]}
      have : F_le F i ≤ S := by
        simp only [F_le, iSup_le_iff]
        intro k hk w hw
        simp only [AddSubgroup.mem_mk, Set.mem_setOf_eq, S]
        let T : AddSubgroup R := {
          carrier := {u | w * u ∈ F_le F (i + j)}
          add_mem' := fun ha hb ↦ by simp only [Set.mem_setOf_eq, mul_add, add_mem ha.out hb.out]
          zero_mem' := by simp only [Set.mem_setOf_eq, mul_zero, zero_mem]
          neg_mem' := by simp only [Set.mem_setOf_eq, mul_neg, neg_mem_iff, imp_self, implies_true]}
        have : F_le F j ≤ T := by
          simp only [F_le, iSup_le_iff]
          intro l hl v hv
          simp only [AddSubgroup.mem_mk, Set.mem_setOf_eq, T]
          have : F (k + l) ≤ ⨆ k, ⨆ (_ : k ≤ i + j), F k := by
            apply le_biSup
            exact add_le_add hk hl
          exact this (SetLike.GradedMul.mul_mem hw hv)
        exact (this hy).out
      exact this hx

end

/-
1. no filALg
2. Gr = > Fil Mod/Alg?

R -> S  <--------
   1             |
FR -> FS         |3
  2              |
GR -> GS --------
1. mpr exhaust
2. done?(before) 2.mpr : this file
3. ???
-/
