import FilteredRing.Filtration_to_Grading




section IsFilteredHom

variable {ι A B α β : Type*} [Preorder ι] [SetLike α A] [SetLike β B]

variable (FA : ι → α) (FA_lt : outParam <| ι → α) (FB : ι → β) (FB_lt : outParam <| ι → β)
  [IsFiltration FA FA_lt] [IsFiltration FB FB_lt]

class IsFilteredHom (f : A → B) : Prop where
  pieces_wise : ∀ i : ι, ∀ a : FA i, f a ∈ FB i

variable {C σ : Type*} [SetLike σ C] (FC : ι → σ) (FC_lt : outParam <| ι → σ)
  [IsFiltration FC FC_lt]

variable (f : A → B) [IsFilteredHom FA FB f] (g : B → C) [IsFilteredHom FB FC g]

include FB in
omit [Preorder ι] in
lemma IsFilteredHom.comp : IsFilteredHom FA FC (g.comp f) :=
  ⟨fun i a ↦ IsFilteredHom.pieces_wise i
    ⟨f a, IsFilteredHom.pieces_wise (FA := FA) (FB := FB) i a⟩⟩

end IsFilteredHom




section

variable {ι R S T γ σ τ : Type*} [OrderedAddCommMonoid ι]

variable [Ring R] [Ring S] [Ring T] [SetLike γ R] [SetLike σ S] [SetLike τ T]

variable (FR : ι → γ) (FR_lt : outParam <| ι → γ) (FS : ι → σ) (FS_lt : outParam <| ι → σ)
(FT : ι → τ) (FT_lt : outParam <| ι → τ)

variable (f : R →+* S) (g : S →+* T) [IsRingFiltration FR FR_lt] [IsRingFiltration FS FS_lt]
[IsRingFiltration FT FT_lt]


section FilteredRingHom

class IsFilteredRingHom extends IsFilteredHom FR FS f

attribute [instance] IsFilteredRingHom.toIsFilteredHom

#check IsFilteredRingHom FR FS f

class FilteredRingHom.IsStrict extends IsFilteredRingHom FR FS f where
  strict : ∀ p : ι, ∀ x : S, x ∈ f '' (FR p) ↔ (x ∈ (FS p) ∧ x ∈ f.range)

variable [IsFilteredRingHom FR FS f] [IsFilteredRingHom FS FT g]

instance : IsFilteredRingHom FR FT (g.comp f) := by
  -- apply IsFilteredRingHom.mk

  -- have : IsFilteredHom FR FT (g.comp f) := by
  --   -- apply?
  --   --   apply?
  --   apply IsFilteredHom.comp FR FS FT f
  --   sorry
  -- exact IsFilteredRingHom.mk
    --   apply?
  -- apply IsFilteredRingHom.mk
  -- apply?
  sorry

end FilteredRingHom

section

variable {R : Type*} [Ring R] (σR : Type*) [SetLike σR R] [AddSubgroupClass σR R]
variable (FR : ι → σR) (FR_lt : outParam <| ι → σR) [fil : IsRingFiltration FR FR_lt]

variable {M : Type*} [AddCommMonoid M] [Module R M] (σM : Type*) [SetLike σM M]
[AddSubmonoidClass σM M] [SMulMemClass σM R M] (FM : ι → σM) (FM_lt : outParam <| ι → σM)

variable {N : Type*} [AddCommMonoid N] [Module R N] (σN : Type*) [SetLike σN N]
[AddSubmonoidClass σN N] [SMulMemClass σN R N] (FN : ι → σN) (FN_lt : outParam <| ι → σN)
(f : M →ₗ[R] N)


class IsFilteredModuleHom : Prop where
  piece_wise : ∀ i : ι, ∀ m ∈ FM i, f m ∈ FN i

end



section DirectSum

variable [AddSubgroupClass γ R] [AddSubgroupClass σ S] [DecidableEq ι]
[IsFilteredRingHom FR FS f] [IsFilteredRingHom FR_lt FS_lt f]


variable [AddSubgroupClass γ R] [AddSubgroupClass σ S] [AddSubgroupClass τ T]
[DecidableEq ι] [IsFilteredRingHom FR FS f] [IsFilteredRingHom FS FT g]

private noncomputable def Gf (i : ι) : GradedPiece FR FR_lt i → GradedPiece FS FS_lt i := by
  intro a
  let h(i) := fun (s : FR i) ↦ GradedPiece.mk FS FS_lt
      ⟨f s, IsFilteredRingHom.toIsFilteredHom.pieces_wise i s⟩

  use Quotient.lift (fun (s : FR i)↦ GradedPiece.mk FS FS_lt
      ⟨f s, IsFilteredRingHom.toIsFilteredHom.pieces_wise i s⟩) ?_ a

  intro a b h
  show GradedPiece.mk FS FS_lt ⟨f a, IsFilteredRingHom.toIsFilteredHom.pieces_wise i a⟩
    = GradedPiece.mk FS FS_lt ⟨f b, IsFilteredRingHom.toIsFilteredHom.pieces_wise i b⟩
  rw [← Quotient.eq_iff_equiv] at h
  have : - a + b ∈ ((FR_lt i) : AddSubgroup R).addSubgroupOf ((FR i) : AddSubgroup R) :=
    QuotientAddGroup.eq.mp h
  apply QuotientAddGroup.eq.mpr
  have : f (- a + b) ∈ (FS_lt i) :=
    IsFilteredRingHom.toIsFilteredHom.pieces_wise i (⟨- a + b, this⟩ : FR_lt i)
  rw [map_add, map_neg] at this
  exact this

open DirectSum in
noncomputable def G : (Graded FR FR_lt) → (Graded FS FS_lt) :=
  fun a ↦
    let _ : (i : ι) → (x : GradedPiece FR FR_lt i) → Decidable (x ≠ 0) := fun _ x ↦
      Classical.propDecidable (x ≠ 0)
    mk (fun i ↦ GradedPiece FS FS_lt i) (DFinsupp.support a)
      <| fun i ↦ (Gf FR FR_lt FS FS_lt f i) (a i)

variable [IsFilteredRingHom FS_lt FT_lt g]


#check (G FS FS_lt FT FT_lt g).comp (G FR FR_lt FS FS_lt f)
#check g.comp f



#check (G FR FR_lt FT FT_lt (g.comp f))
-- variable {f : }

instance : (G FS FS_lt FT FT_lt g).comp (G FR FR_lt FS FS_lt f) = (G FR FR_lt FT FT_lt (g.comp f)) := by

  apply (Set.eqOn_univ (G FS FS_lt FT FT_lt g ∘ G FR FR_lt FS FS_lt f) (G FR FR_lt FT FT_lt (g.comp f))).mp
    fun x a ↦ ? x

  sorry

end DirectSum


section exactness

variable {ι R σ : Type*} [DecidableEq ι] [OrderedAddCommMonoid ι]

variable [Ring R] [SetLike σ R] [AddSubgroupClass σ R]

variable (L M N : ι → σ) (L_lt M_lt N_lt : outParam <| ι → σ)

variable [IsRingFiltration L L_lt] [IsRingFiltration M M_lt] [IsRingFiltration N N_lt]

variable (f g : R →+* R) [IsFilteredRingHom L M f] [IsFilteredRingHom M N g]
[IsFilteredRingHom L_lt M_lt f] [IsFilteredRingHom M_lt N_lt g]

theorem exact_of_exact (exact : Function.Exact f g) (strict : 0 = 0):
  Function.Exact (G L L_lt M M_lt f) (G M M_lt N N_lt g) := by
    sorry





end exactness


end
