import FilteredRing.Basic

universe u v w

set_option linter.unusedSectionVars false

suppress_compilation

variable {R : Type u} [Ring R]

variable {ι : Type v} [OrderedCancelAddCommMonoid ι] [DecidableEq ι]

variable (F : ι → AddSubgroup R) [FilteredRing F]

open BigOperators Pointwise DirectSum

def F_lt (i : ι) := ⨆ k < i, F k

abbrev GradedPiece (i : ι) := (F i) ⧸ (F_lt F i).addSubgroupOf (F i)

instance {i : ι} : AddGroup (GradedPiece F i) := by infer_instance

abbrev GradedPiece' (i : ι) : AddSubgroup (⨁ i, GradedPiece F i) :=
  (DirectSum.of (GradedPiece F) i).range

#check GradedPiece' F
#check ⨁ i, GradedPiece' F i

private abbrev forward (i : ι) : GradedPiece F i → GradedPiece' F i :=
  fun x => ⟨DirectSum.of (GradedPiece F) i x, by simp only [AddMonoidHom.mem_range, exists_apply_eq_apply]⟩

lemma forward_add {i : ι} : ∀ x y, forward F i (x + y) = forward F i x + forward F i y := by
  intros
  simp only [forward, AddMonoidHom.map_add]
  rfl

lemma forward_injective : Function.Injective (forward F i) := by
  intro x y h
  simp only [Subtype.eq_iff] at h
  exact @of_injective _ (GradedPiece F) _ _ i x y h

lemma forward_surjective {i : ι} : Function.Surjective (forward F i) := by
  intro ⟨x', hx⟩
  obtain ⟨x, rfl⟩ := AddMonoidHom.mem_range.mp hx
  use x

lemma forward_bijective {i : ι} : Function.Bijective (forward F i) :=
  ⟨forward_injective F, forward_surjective F⟩

instance gradedPieceAddHom {i : ι} : AddHom (GradedPiece F i) (GradedPiece' F i) where
  toFun := forward F i
  map_add' := forward_add F

instance gradedPieceEquiv {i : ι} : GradedPiece F i ≃ GradedPiece' F i :=
  Equiv.ofBijective (forward F i) (forward_bijective F)

instance gradedPieceAddEquiv {i : ι} : GradedPiece F i ≃+ GradedPiece' F i where
  __ := gradedPieceEquiv F
  __ := gradedPieceAddHom F

-- instance gradedAddEquiv : ⨁ i, GradedPiece F i ≃+ ⨁ i, GradedPiece' F i := sorry
