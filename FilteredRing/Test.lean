import FilteredRing.Filtration_to_Grading




section IsFilteredHom

variable {ι A B C α β σ: Type*} [Preorder ι] [SetLike α A] [SetLike β B] [SetLike σ C]

variable (FA : ι → α) (FA_lt : outParam <| ι → α) [IsFiltration FA FA_lt]
variable (FB : ι → β) (FB_lt : outParam <| ι → β) [IsFiltration FB FB_lt]
variable (FC : ι → σ) (FC_lt : outParam <| ι → σ) [IsFiltration FC FC_lt]

class IsFilteredHom (f : A → B) : Prop where
  pieces_wise : ∀ i : ι, ∀ a : FA i, f a ∈ FB i

variable (f : A → B) [IsFilteredHom FA FB f] (g : B → C) [IsFilteredHom FB FC g]

include FB in
omit [Preorder ι] in
lemma IsFilteredHom.comp : IsFilteredHom FA FC (g.comp f) :=
  ⟨fun i a ↦ IsFilteredHom.pieces_wise i
    ⟨f a, IsFilteredHom.pieces_wise (FA := FA) (FB := FB) i a⟩⟩

end IsFilteredHom




section

variable {ι R S T γ σ τ : Type*} [OrderedAddCommMonoid ι]

variable [Ring R] (FR : ι → γ) (FR_lt : outParam <| ι → γ) [SetLike γ R] [IsRingFiltration FR FR_lt]
variable [Ring S] (FS : ι → σ) (FS_lt : outParam <| ι → σ) [SetLike σ S] [IsRingFiltration FS FS_lt]
variable [Ring T] (FT : ι → τ) (FT_lt : outParam <| ι → τ) [SetLike τ T] [IsRingFiltration FT FT_lt]

variable (f : R →+* S) (g : S →+* T)

section FilteredRingHom

class IsFilteredRingHom extends IsFilteredHom FR FS f

attribute [instance] IsFilteredRingHom.toIsFilteredHom

class FilteredRingHom.IsStrict extends IsFilteredRingHom FR FS f where
  strict : ∀ p : ι, ∀ x : S, x ∈ f '' (FR p) ↔ (x ∈ (FS p) ∧ x ∈ f.range)

variable [IsFilteredRingHom FR FS f] [IsFilteredRingHom FS FT g]

include FS in
omit [OrderedAddCommMonoid ι] in
lemma IsFilteredRingHom.comp : IsFilteredRingHom FR FT (g.comp f) :=
  let _ : IsFilteredHom FR FT (g.comp f) := IsFilteredHom.comp FR FS FT f g
  mk

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

variable [IsFilteredRingHom FR_lt FS_lt f] [IsFilteredRingHom FS_lt FT_lt g]

-- lemma : IsFilteredRingHom FR_lt FT_lt (g.comp f) := by
  -- apply?
  -- exact IsFilteredRingHom.comp FR_lt FS_lt FT_lt f g

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

variable (f g : R →+* R) [IsFilteredRingHom L_lt M_lt f] [IsFilteredRingHom M_lt N_lt g]


theorem exact_of_exact (exact : Function.Exact f g) [FilteredRingHom.IsStrict L M f]
  [FilteredRingHom.IsStrict M N g] : Function.Exact (G L L_lt M M_lt f) (G M M_lt N N_lt g) := by

  have component_exact : ∀ p : ι, ∀ x : M p, (Gf M M_lt N N_lt g) p (Quotient.mk' x) = 0 →
    ∃ y : L p, (Gf L L_lt M M_lt f) p (Quotient.mk' y) = Quotient.mk' x := by
      intro p x noname
      have : ∃ x' : M_lt p, g x = g x' := sorry
      rcases this with ⟨x', geq⟩
      have : ∃ y : L p, f y = x - x' := sorry
      rcases this with ⟨y, feq⟩
      use y
      let _ : (i : ι) → (x : GradedPiece L L_lt i) → Decidable (x ≠ 0) := fun _ x ↦ Classical.propDecidable (x ≠ 0)


      have : ∃ fy : M p, fy = f y := by
        refine CanLift.prf (f ↑y) (IsFilteredHom.pieces_wise p y)

      rcases this with ⟨fy, huh⟩

      #check Quotient.lift_mk (fun (s : L p)↦ GradedPiece.mk M M_lt ⟨f s, IsFilteredRingHom.toIsFilteredHom.pieces_wise p s⟩) ?_ y

      have : (Gf L L_lt M M_lt f) p (Quotient.mk' y) = Quotient.mk' (fy) := by
        unfold Gf
        simp





      sorry
  sorry


end exactness


end
