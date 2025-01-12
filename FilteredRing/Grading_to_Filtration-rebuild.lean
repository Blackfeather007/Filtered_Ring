import FilteredRing.Basic

universe u v w

suppress_compilation

section FilRing
variable {R : Type u} [Ring R] {ι : Type v} [OrderedCancelAddCommMonoid ι] [DecidableEq ι]

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
    is_sup := sorry


end FilRing




-- section FilMod
-- variable {R : Type u} [CommSemiring R]
--   {ι : Type v} [DecidableEq ι] [OrderedAddCommMonoid ι]
--   {A : Type w} [Semiring A] [Algebra R A]
--   {σ : Type*} [SetLike σ A] [AddSubmonoidClass σ A] [CompleteLattice σ]

-- variable (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]

-- def F_le' (F : ι → σ) (i : ι) := ⨆ k ≤ i, F k

-- def induced_fil' (𝒜 : ι → σ) := fun i ↦ F_le' 𝒜 i

-- instance : FilteredAlgebra (induced_fil' 𝒜) where
--   mono := by
--     intro i j h x hx
--     have : ⨆ k ≤ i, 𝒜 k ≤ ⨆ k ≤ j, 𝒜 k :=
--       have : ∀ k ≤ i, 𝒜 k ≤ ⨆ k, ⨆ (_ : k ≤ j), 𝒜 k :=
--         fun k hk ↦ le_biSup 𝒜 (Preorder.le_trans k i j hk h)
--       iSup_le (fun k ↦ iSup_le (fun t ↦ this k t))
--     exact this hx
--   one :=
--     have t1 : 𝒜 0 ≤ ⨆ k, ⨆ (_ : k ≤ 0), 𝒜 k := (le_biSup 𝒜 (Preorder.le_refl 0))
--     have t2 : 1 ≤ 𝒜 0 := Submodule.one_le.mpr SetLike.GradedOne.one_mem
--     Submodule.one_le.mp (t2.trans t1)
--   mul_mem := by
--     intro i j x y hx hy
--     let S : Submodule R A := {
--       carrier := {z | z * y ∈ induced_fil' 𝒜 (i + j)}
--       add_mem' := fun ha hb ↦ by simp only [Set.mem_setOf_eq, add_mul, add_mem ha.out hb.out]
--       zero_mem' := by simp only [Set.mem_setOf_eq, zero_mul, zero_mem]
--       smul_mem' := by
--         intro r a ha
--         simp only [Set.mem_setOf_eq, Algebra.smul_mul_assoc]
--         let P : Submodule R A := {
--           carrier := {p | r • p ∈ induced_fil' 𝒜 (i + j)}
--           add_mem' := fun ha hb ↦ by simp only [Set.mem_setOf_eq, smul_add, add_mem ha.out hb.out]
--           zero_mem' := by simp only [Set.mem_setOf_eq, smul_zero, Submodule.zero_mem]
--           smul_mem' := fun c x hx ↦ by simp only [Set.mem_setOf_eq, smul_comm r c x,
--                         Submodule.smul_mem (induced_fil' 𝒜 (i + j)) c hx] at hx ⊢
--             }
--         have : induced_fil' 𝒜 (i + j) ≤ P := by
--           simp only [induced_fil', F_le', iSup_le_iff]
--           intro l hl q hq
--           simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
--             Set.mem_setOf_eq, P]
--           have t2 : 𝒜 l ≤ ⨆ k, ⨆ (_ : k ≤ i + j), 𝒜 k := by
--             apply le_biSup
--             exact hl
--           exact t2 (Submodule.smul_mem (𝒜 l) r hq)
--         simp only [Set.mem_setOf_eq] at ha
--         exact this ha
--     }
--     have : induced_fil' 𝒜 i ≤ S := by
--       simp only [induced_fil', F_le', iSup_le_iff]
--       intro k hk w hw
--       simp only [AddSubgroup.mem_mk, Set.mem_setOf_eq, S]
--       let T : Submodule R A := {
--         carrier := {u | w * u ∈ induced_fil' 𝒜 (i + j)}
--         add_mem' := fun ha hb ↦ by simp only [Set.mem_setOf_eq, mul_add, add_mem ha.out hb.out]
--         zero_mem' := by simp only [Set.mem_setOf_eq, mul_zero, zero_mem]
--         smul_mem' := by
--           intro c x hx
--           simp only [Set.mem_setOf_eq, Algebra.mul_smul_comm] at hx ⊢
--           let P : Submodule R A := {
--           carrier := {p | c • p ∈ induced_fil' 𝒜 (i + j)}
--           add_mem' := fun ha hb ↦ by simp only [Set.mem_setOf_eq, smul_add, add_mem ha.out hb.out]
--           zero_mem' := by simp only [Set.mem_setOf_eq, smul_zero, Submodule.zero_mem]
--           smul_mem' := fun c₁ x hx ↦ by simp only [Set.mem_setOf_eq, smul_comm c c₁ x,
--               Submodule.smul_mem (induced_fil' 𝒜 (i + j)) c₁ hx] at hx ⊢}
--           have : induced_fil' 𝒜 (i + j) ≤ P := by
--             simp only [induced_fil', F_le', iSup_le_iff]
--             intro l hl q hq
--             simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
--               Set.mem_setOf_eq, P]
--             have t2 : 𝒜 l ≤ ⨆ k, ⨆ (_ : k ≤ i + j), 𝒜 k := by
--               apply le_biSup
--               exact hl
--             exact t2 (Submodule.smul_mem (𝒜 l) c hq)
--           exact this hx}

--       have : induced_fil' 𝒜 j ≤ T := by
--         simp only [induced_fil', F_le', iSup_le_iff]
--         intro l hl v hv
--         simp only [AddSubgroup.mem_mk, Set.mem_setOf_eq, T]
--         have : 𝒜 (k + l) ≤ ⨆ k, ⨆ (_ : k ≤ i + j), 𝒜 k := by
--           apply le_biSup
--           exact add_le_add hk hl
--         apply this (SetLike.GradedMul.mul_mem hw hv)
--       exact (this hy).out
--     exact this hx

-- end FilMod
