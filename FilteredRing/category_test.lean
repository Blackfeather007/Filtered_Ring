import Mathlib

suppress_compilation

universe u v w

open CategoryTheory

namespace CategoryTheory

open SuccOrder

variable (𝓐 : Type u) [Category.{u} 𝓐] [Abelian 𝓐]

variable (ι : Type v) [OrderedAddCommMonoid ι] [SuccOrder ι] [DecidableEq ι]

structure Filtration (A : 𝓐) where
  F : ι → Subobject A
  mono : ∀ i : ι, F i ≤ F (succ i)
  -- whole : iSup F = ⊥
  whole : ∀ i : ι, F i ≤ ⊥

-- def FilteredObject (A : 𝓐) : Type max u v :=
--   ι → Filtration ι A

structure FilteredObject : Type max u v where
  obj : 𝓐
  fil : Filtration 𝓐 ι obj

instance : Category (FilteredObject 𝓐 ι) where
  Hom := by
    intro X Y
    let f : X.obj ⟶ Y.obj := sorry

    sorry
  id := sorry
  comp := sorry

end CategoryTheory

-- instance categoryOfGradedObjects : CategoryStruct (FilteredObject )







-- -- implicit or explicit?
-- variable (C : Type u) [Category.{v} C] [Abelian C]

-- variable (ι : Type v) [OrderedAddCommMonoid ι]
--   [SuccOrder ι] [DecidableEq ι]

-- /- decreasing filtration
-- see [https://stacks.math.columbia.edu/tag/0120]
-- 这里也可以实现成class或者structure, which is better?
-- - class Filtraction (F : ι → Subobject C) where + some properties
-- - structure Filtration where
--     F : ι → Subobject C
--     + some properties
-- -/

-- structure Filtration where
--   F : ι → Subobject C
--   mono : ∀ i : ι, F (succ i) ≤ F i
--   whole : iSup F = ⊥

-- /-
-- 怎么定义这个filtration object比较好
-- 1. 打包成一个pair (A,F)
-- 2. 类似GradedObject的写法写一个map
-- -/
-- structure FilteredObject : Type (max (u + 1) v) where
--   obj : C
--   fil : Filtration C ι

-- instance : CategoryStruct (FilteredObject C ι) where
--   Hom := sorry
--   id := sorry
--   comp := sorry

-- instance : Category (FilteredObject C ι) := sorry
