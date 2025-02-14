import FilteredRing.Filtration_to_Grading

section FilteredHom

variable {ι A B α β : Type*} [Preorder ι] [SetLike α A] [SetLike β B]

class FilteredHom
    (FA : ι → α) (FA_lt : outParam <| ι → α) (FB : ι → β) (FB_lt : outParam <| ι → β)
    [IsFiltration FA FA_lt] [IsFiltration FB FB_lt] (f : A → B) : Prop where
  pieces_wise : ∀ i : ι, ∀ a : FA i, f a ∈ FB i

end FilteredHom

section

variable {ι R S γ σ : Type*} [OrderedAddCommMonoid ι]

variable [Ring R] [Ring S] [SetLike γ R] [SetLike σ S]

variable (FR : ι → γ) (FR_lt : outParam <| ι → γ) (FS : ι → σ) (FS_lt : outParam <| ι → σ)

variable (f : R →+* S) [IsRingFiltration FR FR_lt] [IsRingFiltration FS FS_lt]

section FilteredRingHom

class FilteredRingHom extends FilteredHom FR FR_lt FS FS_lt f

class StrictFilteredRingHom extends FilteredRingHom FR FR_lt FS FS_lt f where
  strict : ∀ p : ι, ∀ x : S, x ∈ f '' (FR p) ↔ (x ∈ (FS p) ∧ x ∈ f.range)

end FilteredRingHom

section

variable {R : Type*} [Ring R] (σR : Type*) [SetLike σR R] [AddSubgroupClass σR R]
variable (FR : ι → σR) (FR_lt : outParam <| ι → σR) [fil : IsRingFiltration FR FR_lt]

variable {M : Type*} [AddCommMonoid M] [Module R M] (σM : Type*) [SetLike σM M]
[AddSubmonoidClass σM M] [SMulMemClass σM R M] (FM : ι → σM) (FM_lt : outParam <| ι → σM)

variable {N : Type*} [AddCommMonoid N] [Module R N] (σN : Type*) [SetLike σN N]
[AddSubmonoidClass σN N] [SMulMemClass σN R N] (FN : ι → σN) (FN_lt : outParam <| ι → σN)
(f : M →ₗ[R] N)


class FilteredModuleHom : Prop where
  piece_wise : ∀ i : ι, ∀ m ∈ FM i, f m ∈ FN i

end



section DirectSum

variable [AddSubgroupClass γ R] [AddSubgroupClass σ S] [DecidableEq ι] [FilteredRingHom FR FR_lt FS FS_lt f]

private noncomputable def Gf (i : ι) : GradedPiece FR FR_lt i → GradedPiece FS FS_lt i :=
  fun a ↦ let s := Quotient.out' a
    GradedPiece.mk FS FS_lt
      ⟨f s, FilteredRingHom.toFilteredHom.pieces_wise i s (FB_lt := FS_lt)⟩

open DirectSum in
noncomputable def G : (⨁ i, GradedPiece FR FR_lt i) → (⨁ i, GradedPiece FS FS_lt i) :=
  fun a ↦
    let _ : (i : ι) → (x : GradedPiece FR FR_lt i) → Decidable (x ≠ 0) := fun _ x ↦
      Classical.propDecidable (x ≠ 0)
    mk (fun i ↦ GradedPiece FS FS_lt i) (DFinsupp.support a)
      <| fun i ↦ (Gf FR FR_lt FS FS_lt f i) (a i)

end DirectSum

section exactness

variable {ι R σ : Type*} [DecidableEq ι] [OrderedAddCommMonoid ι]

variable [Ring R] [SetLike σ R] [AddSubgroupClass σ R]

variable (L M N : ι → σ) (L_lt M_lt N_lt : outParam <| ι → σ)

variable [IsRingFiltration L L_lt] [IsRingFiltration M M_lt] [IsRingFiltration N N_lt]

variable (f g : R →+* R) [FilteredRingHom L L_lt M M_lt f] [FilteredRingHom M M_lt N N_lt g]

theorem exact_of_exact (exact : Function.Exact f g) (strict : 0 = 0):
  Function.Exact (G L L_lt M M_lt f) (G M M_lt N N_lt g) := by
    sorry





end exactness


end
