import FilteredRing.Basic
universe u v w

suppress_compilation

section FilRing
variable {R : Type u} [Ring R]
  {ι : Type v} [OrderedCancelAddCommMonoid ι]  [DecidableEq ι]
  {σ : Type w} [SetLike σ R] [AddSubmonoidClass σ R]
  [CompleteLattice σ] (F : ι → σ) [fil : FilteredRing F]

def F_le (i : ι) := ⨆ k ≤ i, F k

def F_lt (i : ι) := ⨆ k < i, F k

def induced_fil (R₀ : ι → AddSubgroup R) : ι → AddSubgroup R := fun i ↦ F_le R₀ i

instance Graded_to_Filtered (R₀ : ι → AddSubgroup R) [GradedRing R₀] :
    FilteredRing (induced_fil R₀) where
  mono := by
    intro i j h x hx
    have : ⨆ k ≤ i, R₀ k ≤ ⨆ k ≤ j, R₀ k :=
      have : ∀ k ≤ i, R₀ k ≤ ⨆ k, ⨆ (_ : k ≤ j), R₀ k :=
        fun k hk ↦ le_biSup R₀ (Preorder.le_trans k i j hk h)
      iSup_le (fun k ↦ iSup_le (fun t ↦ this k t))
    exact this hx
  one :=
    have : R₀ 0 ≤ ⨆ k, ⨆ (_ : k ≤ 0), R₀ k := (le_biSup R₀ (Preorder.le_refl 0))
    this SetLike.GradedOne.one_mem
  mul_mem := by
    intro i j x y hx hy
    let S : AddSubgroup R := {
      carrier := {z | z * y ∈ induced_fil R₀ (i + j)}
      add_mem' := fun ha hb ↦ by simp only [Set.mem_setOf_eq, add_mul, add_mem ha.out hb.out]
      zero_mem' := by simp only [Set.mem_setOf_eq, zero_mul, zero_mem]
      neg_mem' := by simp only [Set.mem_setOf_eq, neg_mul, neg_mem_iff, imp_self, implies_true]}
    have : induced_fil R₀ i ≤ S := by
      simp only [induced_fil, F_le, iSup_le_iff]
      intro k hk w hw
      simp only [AddSubgroup.mem_mk, Set.mem_setOf_eq, S]
      let T : AddSubgroup R := {
        carrier := {u | w * u ∈ induced_fil R₀ (i + j)}
        add_mem' := fun ha hb ↦ by simp only [Set.mem_setOf_eq, mul_add, add_mem ha.out hb.out]
        zero_mem' := by simp only [Set.mem_setOf_eq, mul_zero, zero_mem]
        neg_mem' := by simp only [Set.mem_setOf_eq, mul_neg, neg_mem_iff, imp_self, implies_true]}
      have : induced_fil R₀ j ≤ T := by
        simp only [induced_fil, F_le, iSup_le_iff]
        intro l hl v hv
        simp only [AddSubgroup.mem_mk, Set.mem_setOf_eq, T]
        have : R₀ (k + l) ≤ ⨆ k, ⨆ (_ : k ≤ i + j), R₀ k := by
          apply le_biSup
          exact add_le_add hk hl
        exact this (SetLike.GradedMul.mul_mem hw hv)
      exact (this hy).out
    exact this hx

end FilRing




section FilMod
variable {R : Type u} [CommSemiring R]
  {ι : Type v} [DecidableEq ι] [OrderedAddCommMonoid ι]
  {A : Type w} [Semiring A] [Algebra R A]
  {σ : Type*} [SetLike σ A] [AddSubmonoidClass σ A] [CompleteLattice σ]

variable (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]

def F_le' (F : ι → σ) (i : ι) := ⨆ k ≤ i, F k

def induced_fil' (𝒜 : ι → σ) := fun i ↦ F_le' 𝒜 i

instance : FilteredAlgebra (induced_fil' 𝒜) where
  mono := by
    intro i j h x hx
    have : ⨆ k ≤ i, 𝒜 k ≤ ⨆ k ≤ j, 𝒜 k :=
      have : ∀ k ≤ i, 𝒜 k ≤ ⨆ k, ⨆ (_ : k ≤ j), 𝒜 k :=
        fun k hk ↦ le_biSup 𝒜 (Preorder.le_trans k i j hk h)
      iSup_le (fun k ↦ iSup_le (fun t ↦ this k t))
    exact this hx
  one :=
    have t1 : 𝒜 0 ≤ ⨆ k, ⨆ (_ : k ≤ 0), 𝒜 k := (le_biSup 𝒜 (Preorder.le_refl 0))
    have t2 : 1 ≤ 𝒜 0 := Submodule.one_le.mpr SetLike.GradedOne.one_mem
    Submodule.one_le.mp (t2.trans t1)
  mul_mem := by
    intro i j x y hx hy
    let S : Submodule R A := {
      carrier := {z | z * y ∈ induced_fil' 𝒜 (i + j)}
      add_mem' := fun ha hb ↦ by simp only [Set.mem_setOf_eq, add_mul, add_mem ha.out hb.out]
      zero_mem' := by simp only [Set.mem_setOf_eq, zero_mul, zero_mem]
      smul_mem' := by
        intro r a ha
        simp only [Set.mem_setOf_eq, Algebra.smul_mul_assoc]
        let P : Submodule R A := {
          carrier := {p | r • p ∈ induced_fil' 𝒜 (i + j)}
          add_mem' := fun ha hb ↦ by simp only [Set.mem_setOf_eq, smul_add, add_mem ha.out hb.out]
          zero_mem' := by simp only [Set.mem_setOf_eq, smul_zero, Submodule.zero_mem]
          smul_mem' := fun c x hx ↦ by simp only [Set.mem_setOf_eq, smul_comm r c x,
                        Submodule.smul_mem (induced_fil' 𝒜 (i + j)) c hx] at hx ⊢
            }
        have : induced_fil' 𝒜 (i + j) ≤ P := by
          simp only [induced_fil', F_le', iSup_le_iff]
          intro l hl q hq
          simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
            Set.mem_setOf_eq, P]
          have t2 : 𝒜 l ≤ ⨆ k, ⨆ (_ : k ≤ i + j), 𝒜 k := by
            apply le_biSup
            exact hl
          exact t2 (Submodule.smul_mem (𝒜 l) r hq)
        simp only [Set.mem_setOf_eq] at ha
        exact this ha
    }
    have : induced_fil' 𝒜 i ≤ S := by
      simp only [induced_fil', F_le', iSup_le_iff]
      intro k hk w hw
      simp only [AddSubgroup.mem_mk, Set.mem_setOf_eq, S]
      let T : Submodule R A := {
        carrier := {u | w * u ∈ induced_fil' 𝒜 (i + j)}
        add_mem' := fun ha hb ↦ by simp only [Set.mem_setOf_eq, mul_add, add_mem ha.out hb.out]
        zero_mem' := by simp only [Set.mem_setOf_eq, mul_zero, zero_mem]
        smul_mem' := by
          intro c x hx
          simp only [Set.mem_setOf_eq, Algebra.mul_smul_comm] at hx ⊢
          let P : Submodule R A := {
          carrier := {p | c • p ∈ induced_fil' 𝒜 (i + j)}
          add_mem' := fun ha hb ↦ by simp only [Set.mem_setOf_eq, smul_add, add_mem ha.out hb.out]
          zero_mem' := by simp only [Set.mem_setOf_eq, smul_zero, Submodule.zero_mem]
          smul_mem' := fun c₁ x hx ↦ by simp only [Set.mem_setOf_eq, smul_comm c c₁ x,
              Submodule.smul_mem (induced_fil' 𝒜 (i + j)) c₁ hx] at hx ⊢}
          have : induced_fil' 𝒜 (i + j) ≤ P := by
            simp only [induced_fil', F_le', iSup_le_iff]
            intro l hl q hq
            simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
              Set.mem_setOf_eq, P]
            have t2 : 𝒜 l ≤ ⨆ k, ⨆ (_ : k ≤ i + j), 𝒜 k := by
              apply le_biSup
              exact hl
            exact t2 (Submodule.smul_mem (𝒜 l) c hq)
          exact this hx}

      have : induced_fil' 𝒜 j ≤ T := by
        simp only [induced_fil', F_le', iSup_le_iff]
        intro l hl v hv
        simp only [AddSubgroup.mem_mk, Set.mem_setOf_eq, T]
        have : 𝒜 (k + l) ≤ ⨆ k, ⨆ (_ : k ≤ i + j), 𝒜 k := by
          apply le_biSup
          exact add_le_add hk hl
        apply this (SetLike.GradedMul.mul_mem hw hv)
      exact (this hy).out
    exact this hx

end FilMod

-- section Graded

-- def gradedMul {i j : ι} : GradedPiece F i → GradedPiece F j → GradedPiece F (i + j) := by
--   intro x y
--   refine Quotient.map₂' (fun x y ↦ ⟨x.1 * y.1, fil.mul_mem x.2 y.2⟩)
--     ?_ x y
--   intro x₁ x₂ hx y₁ y₂ hy
--   simp [QuotientAddGroup.leftRel_apply, AddSubgroup.mem_addSubgroupOf] at hx hy ⊢
--   have eq : - (x₁.1 * y₁) + x₂ * y₂ = (- x₁ + x₂) * y₁ + x₂ * (- y₁ + y₂) := by noncomm_ring
--   rw [eq]
--   exact add_mem (Filtration.flt_mul_mem hx y₁.2) (Filtration.mul_flt_mem x₂.2 hy)

-- instance : GradedMonoid.GMul (GradedPiece F) where
--   mul := gradedMul F

-- instance : GradedMonoid.GOne (GradedPiece F) where
--   one := by sorry


-- instance : DirectSum.GSemiring (GradedPiece F) where
--   mul_zero := by
--     intro i j a
--     show gradedMul F a (0 : GradedPiece F j) = 0
--     unfold gradedMul
--     rw [← QuotientAddGroup.mk_zero, ← QuotientAddGroup.mk_zero]
--     induction a using Quotient.ind'
--     change Quotient.mk'' _ = Quotient.mk'' _
--     rw [Quotient.eq'']
--     simp [QuotientAddGroup.leftRel_apply, AddSubgroup.mem_addSubgroupOf]
--     exact zero_mem _
--   zero_mul := by sorry
--   mul_add := by
--     intro i j a b c
--     show gradedMul F a (b + c) = gradedMul F a b + gradedMul F a c
--     unfold gradedMul
--     induction a using Quotient.ind'
--     induction b using Quotient.ind'
--     induction c using Quotient.ind'
--     change Quotient.mk'' _ = Quotient.mk'' _
--     rw [Quotient.eq'']
--     simp [QuotientAddGroup.leftRel_apply, AddSubgroup.mem_addSubgroupOf]
--     rw [mul_add, neg_add_eq_zero.mpr]
--     exact zero_mem _
--     rfl
--   add_mul := sorry
--   one_mul := sorry
--   mul_one := sorry
--   mul_assoc := sorry
--   gnpow := sorry
--   gnpow_zero' := sorry
--   gnpow_succ' := sorry
--   natCast := sorry
--   natCast_zero := sorry
--   natCast_succ := sorry

-- end Graded

-- section integer
-- variable [DecidableEq ι] {i : ι}
-- #check DirectSum.of (GradedPiece F) i

-- variable (F : ℤ → AddSubgroup R) [fil : FilteredRing (fun i ↦ (F i).toAddSubmonoid)] (i : ℤ)
-- abbrev GradedPieces := GradedPiece F '' Set.univ

-- @[simp]
-- theorem fil_Z (i : ℤ) : F_lt F i = F (i - 1) := by
--   dsimp [F_lt]
--   ext x
--   simp only [Iff.symm Int.le_sub_one_iff]
--   constructor
--   · exact fun hx ↦ by (
--     have : ⨆ i_1, ⨆ (_ : i_1 ≤ i - 1), F i_1 ≤ F (i - 1) := iSup_le (fun k ↦ iSup_le fil.mono)
--     exact this hx)
--   · intro hx
--     have : F (i - 1) ≤ ⨆ k, ⨆ (_ : k ≤ i - 1), F k := by
--       apply le_iSup_of_le (i - 1)
--       simp only [le_refl, iSup_pos]
--     exact this hx

-- @[simp]
-- theorem GradedPiece_Z (i : ℤ) : GradedPiece F i = ((F i) ⧸ (F (i - 1)).addSubgroupOf (F i)) := by
--   simp only [GradedPiece, fil_Z]

-- end integer

-- instance : Semiring (⨁ i, GradedPiece F i) := by infer_instance

-- variable {i : ι}
-- #check DirectSum.of (GradedPiece F) i

-- abbrev GradedPieces := GradedPiece F '' Set.univ


-- instance : SetLike (GradedPieces F) (⨁ i, GradedPiece F i) where
--   coe := by
--     intro x

--     sorry
--   coe_injective' := sorry

/-
variable [PredOrder ι]
abbrev GradedPiece (i : ι) : Type u := (F i) ⧸ (F (Order.pred i)).addSubgroupOf (F i)

def gradedMul {i j : ι} : GradedPiece F i → GradedPiece F j → GradedPiece F (i + j) := by
  intro x y
  refine Quotient.map₂' (fun x y ↦ ⟨x.1 * y.1, Filtration.mul_mem F i j (Set.mul_mem_mul x.2 y.2)⟩)
    ?_ x y
  intro x₁ x₂ hx y₁ y₂ hy
  simp [QuotientAddGroup.leftRel_apply, AddSubgroup.mem_addSubgroupOf] at hx hy ⊢
  have eq : - (x₁.1 * y₁) + x₂ * y₂ = (- x₁ + x₂) * y₁ + x₂ * (- y₁ + y₂) := by noncomm_ring
  rw [eq]
  obtain h1 := Filtration.mul_mem F (Order.pred i) j (Set.mul_mem_mul hx y₁.2)
  obtain h2 := Filtration.mul_mem F i (Order.pred j) (Set.mul_mem_mul x₂.2 hy)

  have le1 : (AddSubgroup.map (F i).subtype (F_lt F i) : Set R) * F j ≤ ((AddSubgroup.map (F (i + j)).subtype (F_lt F (i + j)) : Set R)) := by
    sorry
  have : Order.pred i + j ≤ Order.pred (i + j) := by
    apply PredOrder.le_pred_of_lt
    sorry
  sorry


  -- have : x.out'.1 ∈ F i := x.out'.2
  -- obtain hh := Filtration.mul_mem F i j (Set.mul_mem_mul x.out'.2 y.out'.2)
  -- let z : F (i + j) := ⟨_, hh⟩
  -- exact @QuotientAddGroup.mk' (F (i + j)) _ ((F (Order.pred (i + j))).addSubgroupOf (F (i + j))) _ z

instance (F : ι → AddSubgroup R) [FilteredRing F] : DirectSum.GSemiring (GradedPiece F) where
  mul := gradedMul F
  mul_zero a := by

    sorry
  zero_mul := sorry
  mul_add := sorry
  add_mul := sorry
  one := sorry
  one_mul := sorry
  mul_one := sorry
  mul_assoc := sorry
  gnpow := sorry
  gnpow_zero' := sorry
  gnpow_succ' := sorry
  natCast := sorry
  natCast_zero := sorry
  natCast_succ := sorry


-- open AddSubgroup PredOrder

-- variable {R : Type u} [Ring R]

-- variable {ι : Type v} [OrderedAddCommMonoid ι] [DecidableEq ι] [PredOrder ι]

-- -- def aux (F : ι → AddSubgroup R) [FilteredRing F] (i : ι) : AddSubgroup R :=
-- --   match decEq i (Order.pred i) with
-- --   | isTrue _ => ⊥
-- --   | isFalse _ => F (Order.pred i)
-/
