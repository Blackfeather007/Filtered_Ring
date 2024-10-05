import FilteredRing.Basic

universe u v w

suppress_compilation

variable {R : Type u} [Ring R]

variable {ι : Type v} [OrderedAddCommMonoid ι] [DecidableEq ι] [PredOrder ι]

variable (F : ι → AddSubgroup R) [fil : FilteredRing F]

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
  have : Order.pred i + j ≤ Order.pred (i + j) := sorry
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

-- variable {i : ι}

-- def gradedMap (F : ι → AddSubgroup R) [fil : FilteredRing R F] (i : ι) : AddSubgroup R := by
--   let aux : (F i) ⧸ (F (pred i)).addSubgroupOf (F i) →+ R :=
--     { toFun := fun x => x.out'.1
--       map_zero' := by
--         dsimp

--         sorry
--       map_add' := by
--         dsimp
--         sorry }
--   exact AddMonoidHom.range aux


-- -- instance : GradedRing (gradedMap F) := sorry

-- variable (F  : ι → AddSubgroup R) [FilteredRing R F] {i : ι}
-- #check GradedRing


-- #check QuotientAddGroup.Quotient.addGroup
-- #check QuotientAddGroup.mk'

-- #check AddSubgroup.map
-- #check QuotientAddGroup.mk' (F i)
-- #check AddSubgroup.map (QuotientAddGroup.mk' (F i)) (F i)
