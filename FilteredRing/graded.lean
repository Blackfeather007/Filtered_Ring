import FilteredRing.Basic

universe u v w

suppress_compilation

variable {R : Type u} [Ring R]

variable {ι : Type v} [OrderedCancelAddCommMonoid ι] [DecidableEq ι]

variable (F : ι → AddSubgroup R) [fil : FilteredRing F]

open BigOperators Pointwise

def F_lt (i : ι) := ⨆ k < i, F k

abbrev GradedPiece (i : ι) : Type u := (F i) ⧸ (F_lt F i).addSubgroupOf (F i)

protected lemma Filtration.iSup_le {i : ι} : ⨆ k < i, F k ≤ F i :=
  iSup_le fun k ↦ iSup_le fun hk ↦ FilteredRing.mono k (le_of_lt hk)

protected lemma Filtration.iSup_le' {i : ι} : ⨆ k < i, (F k : Set R) ≤ F i :=
  iSup_le fun k ↦ iSup_le fun hk ↦ FilteredRing.mono k (le_of_lt hk)

variable {F} in
lemma Filtration.flt_mul_mem {i j : ι} {x y} (hx : x ∈ F_lt F i) (hy : y ∈ F j) :
    x * y ∈ F_lt F (i + j) := by
  rw [F_lt, iSup_subtype'] at hx ⊢
  induction hx using AddSubgroup.iSup_induction' with
  | hp i x hx =>
    exact AddSubgroup.mem_iSup_of_mem ⟨i + j, add_lt_add_right i.2 _⟩ (FilteredRing.mul_mem hx hy)
  | h1 =>
    rw [zero_mul]
    exact zero_mem _
  | hmul _ _ _ _ ih₁ ih₂ =>
    rw [add_mul]
    exact add_mem ih₁ ih₂

variable {F} in
lemma Filtration.mul_flt_mem {i j : ι} {x y} (hx : x ∈ F i) (hy : y ∈ F_lt F j) :
    x * y ∈ F_lt F (i + j) := by
  rw [F_lt, iSup_subtype'] at hy ⊢
  induction hy using AddSubgroup.iSup_induction' with
  | hp j y hy =>
    exact AddSubgroup.mem_iSup_of_mem ⟨i + j, add_lt_add_left j.2 _⟩ (FilteredRing.mul_mem hx hy)
  | h1 =>
    rw [mul_zero]
    exact zero_mem _
  | hmul _ _ _ _ ih₁ ih₂ =>
    rw [mul_add]
    exact add_mem ih₁ ih₂

def gradedMul {i j : ι} : GradedPiece F i → GradedPiece F j → GradedPiece F (i + j) := by
  intro x y
  refine Quotient.map₂' (fun x y ↦ ⟨x.1 * y.1, FilteredRing.mul_mem x.2 y.2⟩)
    ?_ x y
  intro x₁ x₂ hx y₁ y₂ hy
  simp [QuotientAddGroup.leftRel_apply, AddSubgroup.mem_addSubgroupOf] at hx hy ⊢
  have eq : - (x₁.1 * y₁) + x₂ * y₂ = (- x₁ + x₂) * y₁ + x₂ * (- y₁ + y₂) := by noncomm_ring
  rw [eq]
  exact add_mem (Filtration.flt_mul_mem hx y₁.2) (Filtration.mul_flt_mem x₂.2 hy)

instance : DirectSum.GSemiring (GradedPiece F) where
  mul := gradedMul F
  mul_zero a := sorry
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
