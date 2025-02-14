import FilteredRing.Filtration_to_Grading


section FilteredHom

variable {ι A B C α β σ: Type*} [Preorder ι] [SetLike α A] [SetLike β B] [SetLike σ C]

variable (FA : ι → α) (FA_lt : outParam <| ι → α) [IsFiltration FA FA_lt]
variable (FB : ι → β) (FB_lt : outParam <| ι → β) [IsFiltration FB FB_lt]
variable (FC : ι → σ) (FC_lt : outParam <| ι → σ) [IsFiltration FC FC_lt]

class FilteredHom where
  toFun : A → B
  pieces_wise : ∀ i : ι, ∀ a ∈ FA i, toFun a ∈ FB i
  pieces_wise_lt : ∀ i : ι, ∀ a ∈ FA_lt i, toFun a ∈ FB_lt i

variable (f : FilteredHom FA FA_lt FB FB_lt) (g : FilteredHom FB FB_lt FC FC_lt)

variable {FA FB FC FA_lt FB_lt FC_lt} in
def FilteredHom.comp : FilteredHom FA FA_lt FC FC_lt := {
  toFun := g.1.comp f.1
  pieces_wise := fun i a ha ↦ g.pieces_wise i (f.1 a) (f.pieces_wise i a ha)
  pieces_wise_lt := fun i a ha ↦ g.pieces_wise_lt i (f.1 a) (f.pieces_wise_lt i a ha)
}

infixl:100 "∘" => FilteredHom.comp

#check f ∘ g

end FilteredHom


section Main

variable {ι R S T γ σ τ : Type*} [OrderedAddCommMonoid ι]

variable [Ring R] (FR : ι → γ) (FR_lt : outParam <| ι → γ) [SetLike γ R]
  [IsRingFiltration FR FR_lt]
variable [Ring S] (FS : ι → σ) (FS_lt : outParam <| ι → σ) [SetLike σ S]
  [IsRingFiltration FS FS_lt]
variable [Ring T] (FT : ι → τ) (FT_lt : outParam <| ι → τ) [SetLike τ T]
  [IsRingFiltration FT FT_lt]

variable (f : R →+* S) (g : S →+* T)

section FilteredRingHom

class FilteredRingHom extends FilteredHom FR FR_lt FS FS_lt, R →+* S

variable {FR FS FR_lt FS_lt} in
def FilteredRingHom.IsStrict (f : FilteredRingHom FR FR_lt FS FS_lt) : Prop :=
  ∀ p : ι, ∀ x : S, x ∈ f.toFun '' (FR p) ↔ (x ∈ (FS p) ∧ x ∈ f.range)

variable (f : FilteredRingHom FR FR_lt FS FS_lt) (g : FilteredRingHom FS FS_lt FT FT_lt)

variable {FR FS FT FR_lt FS_lt FT_lt} in
def FilteredRingHom.comp : FilteredRingHom FR FR_lt FT FT_lt := {
    g.toRingHom.comp f.toRingHom with
  pieces_wise := fun i a ha ↦ g.pieces_wise i (f.toFun a) (f.pieces_wise i a ha)
  pieces_wise_lt := fun i a ha ↦ g.pieces_wise_lt i (f.toFun a) (f.pieces_wise_lt i a ha)
}

infixl:100 "∘" => FilteredRingHom.comp

#check f ∘ g

end FilteredRingHom

section FilteredModuleHom

variable {R : Type*} [Ring R] (σR : Type*) [SetLike σR R] [AddSubgroupClass σR R]
variable (FR : ι → σR) (FR_lt : outParam <| ι → σR) [fil : IsRingFiltration FR FR_lt]

variable {M : Type*} [AddCommMonoid M] [Module R M] (σM : Type*) [SetLike σM M]
[AddSubmonoidClass σM M] [SMulMemClass σM R M] (FM : ι → σM) (FM_lt : outParam <| ι → σM)

variable {N : Type*} [AddCommMonoid N] [Module R N] (σN : Type*) [SetLike σN N]
[AddSubmonoidClass σN N] [SMulMemClass σN R N] (FN : ι → σN) (FN_lt : outParam <| ι → σN)
(f : M →ₗ[R] N)

class FilteredModuleHom extends FilteredHom FM FM_lt FN FN_lt, M →ₗ[R] N

end FilteredModuleHom


section DirectSum

variable [AddSubgroupClass γ R] [AddSubgroupClass σ S] [AddSubgroupClass τ T] [DecidableEq ι]
  (f : FilteredRingHom FR FR_lt FS FS_lt)
  (g : FilteredRingHom FS FS_lt FT FT_lt)

variable {FR FR_lt FS FS_lt} in
private def Gf (i : ι) : GradedPiece FR FR_lt i → GradedPiece FS FS_lt i := by
  intro a
  let h(i) := fun (s : FR i) ↦ GradedPiece.mk FS FS_lt
      ⟨f.toRingHom s, f.pieces_wise i s (SetLike.coe_mem s)⟩
  use Quotient.lift (fun (s : FR i)↦ GradedPiece.mk FS FS_lt
      ⟨f.toRingHom s, f.pieces_wise i s (SetLike.coe_mem s)⟩) (fun a b h ↦ ?_) a
  show GradedPiece.mk FS FS_lt ⟨f.toRingHom a, f.pieces_wise i a (SetLike.coe_mem a)⟩
    = GradedPiece.mk FS FS_lt ⟨f.toRingHom b, f.pieces_wise i b (SetLike.coe_mem b)⟩
  rw [← Quotient.eq_iff_equiv] at h
  have : - a + b ∈ ((FR_lt i) : AddSubgroup R).addSubgroupOf (FR i : AddSubgroup R) :=
    QuotientAddGroup.eq.mp h
  apply QuotientAddGroup.eq.mpr
  have : f.toRingHom (- a + b) ∈ (FS_lt i) :=
    f.pieces_wise_lt i (⟨- a + b, this⟩ : FR_lt i) this
  rw [map_add, map_neg] at this
  exact this

open DirectSum in
variable {FR FR_lt FS FS_lt} in
noncomputable def G : (Graded FR FR_lt) → (Graded FS FS_lt) :=
  fun a ↦
    let _ : (i : ι) → (x : GradedPiece FR FR_lt i) → Decidable (x ≠ 0) := fun _ x ↦
      Classical.propDecidable (x ≠ 0)
    mk (fun i ↦ GradedPiece FS FS_lt i) (DFinsupp.support a)
      <| fun i ↦ (Gf f i) (a i)

-- lemma : IsFilteredRingHom FR_lt FT_lt (g.comp f) := by
  -- apply?
  -- exact IsFilteredRingHom.comp FR_lt FS_lt FT_lt f g

-- instance : (G g).comp (G f) = (G (g ∘ f)) := by

--   apply (Set.eqOn_univ (G FS FS_lt FT FT_lt g ∘ G FR FR_lt FS FS_lt f) (G FR FR_lt FT FT_lt (g.comp f))).mp
--     fun x a ↦ ? x

--   sorry

end DirectSum


section exactness

variable {ι R σ : Type*} [DecidableEq ι] [OrderedAddCommMonoid ι]

variable [Ring R] [SetLike σ R] [AddSubgroupClass σ R]

variable (L M N : ι → σ) (L_lt M_lt N_lt : outParam <| ι → σ)

variable [IsRingFiltration L L_lt] [IsRingFiltration M M_lt] [IsRingFiltration N N_lt]

variable (f : FilteredRingHom L L_lt M M_lt) (g : FilteredRingHom M M_lt N N_lt)

theorem exact_of_exact (exact : Function.Exact f.toRingHom g.toRingHom) (strict : 0 = 0) :
    Function.Exact (G f) (G g) := by
  have component_exact : ∀ p : ι, ∀ x : M p, (Gf g p) (Quotient.mk' x) = 0 →
      ∃ y : L p, (Gf f p) (Quotient.mk' y) = Quotient.mk' x := by
    intro p x noname
    have : ∃ x' : M_lt p, g.toRingHom x = g.toRingHom x' := sorry
    rcases this with ⟨x', geq⟩
    have : ∃ y : L p, f.toRingHom y = x - x' := sorry
    rcases this with ⟨y, feq⟩
    use y
    let _ : (i : ι) → (x : GradedPiece L L_lt i) → Decidable (x ≠ 0) := fun _ x ↦ Classical.propDecidable (x ≠ 0)


    have : ∃ fy : M p, fy = f.toRingHom y := by
      refine CanLift.prf (f.toRingHom y)
        (f.pieces_wise p y (SetLike.coe_mem y))

    rcases this with ⟨fy, huh⟩

    #check Quotient.lift_mk (fun (s : L p)↦ GradedPiece.mk M M_lt ⟨f.toRingHom s, f.pieces_wise p s (SetLike.coe_mem s)⟩) ?_ y

    have : (Gf f p) (Quotient.mk' y) = Quotient.mk' (fy) := by
      unfold Gf
      simp





      sorry
    sorry



end exactness


end Main
