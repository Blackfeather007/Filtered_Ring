import FilteredRing.Filtration_to_Grading

section FilteredHom

variable {ι A B α β : Type*} [Preorder ι] [SetLike α A] [SetLike β B]

class FilteredHom
    (FA : ι → α) (FA_lt : outParam <| ι → α) (FB : ι → β) (FB_lt : outParam <| ι → β)
    [IsFiltration FA FA_lt] [IsFiltration FB FB_lt] (f : A → B) : Prop where
  pieces_wise : ∀ i : ι, ∀ a : FA i, f a ∈ FB i

end FilteredHom

section FilteredRingHom

variable {ι R S γ σ : Type*} [OrderedAddCommMonoid ι]

variable [Ring R] [Ring S] [SetLike γ R] [SetLike σ S]

variable (FR : ι → γ) (FR_lt : outParam <| ι → γ) (FS : ι → σ) (FS_lt : outParam <| ι → σ)

variable (f : R →+* S) [IsRingFiltration FR FR_lt] [IsRingFiltration FS FS_lt]

class FilteredRingHom extends FilteredHom FR FR_lt FS FS_lt f

variable [AddSubgroupClass γ R] [AddSubgroupClass σ S] [DecidableEq ι]

private def Gf (i : ι) : GradedPiece FR FR_lt i → GradedPiece FS FS_lt i := by
  intro a
  let s := Quotient.out' a
  simp at s
  let s' := f s


  sorry

open DirectSum in
noncomputable def G : (⨁ i, GradedPiece FR FR_lt i) → (⨁ i, GradedPiece FS FS_lt i) := by
  intro a
  let _ : (i : ι) → (x : GradedPiece FR FR_lt i) → Decidable (x ≠ 0) := fun i x ↦
    Classical.propDecidable (x ≠ 0)
  let s := DFinsupp.support a
  exact mk (fun i ↦ GradedPiece FS FS_lt i) s (fun i ↦ (Gf FR FR_lt FS FS_lt i) (a i))

end FilteredRingHom
