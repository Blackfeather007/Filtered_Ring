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

variable (g : FilteredHom FB FB_lt FC FC_lt) (f : FilteredHom FA FA_lt FB FB_lt)

variable {FA FB FC FA_lt FB_lt FC_lt} in
def FilteredHom.comp : FilteredHom FA FA_lt FC FC_lt := {
  toFun := g.1.comp f.1
  pieces_wise := fun i a ha ↦ g.pieces_wise i (f.1 a) (f.pieces_wise i a ha)
  pieces_wise_lt := fun i a ha ↦ g.pieces_wise_lt i (f.1 a) (f.pieces_wise_lt i a ha)
}

infixl:100 " ∘ " => FilteredHom.comp

end FilteredHom


section Def

variable {ι R S T γ σ τ : Type*} [OrderedAddCommMonoid ι]

variable [Ring R] (FR : ι → γ) (FR_lt : outParam <| ι → γ) [SetLike γ R]
  [IsRingFiltration FR FR_lt]
variable [Ring S] (FS : ι → σ) (FS_lt : outParam <| ι → σ) [SetLike σ S]
  [IsRingFiltration FS FS_lt]
variable [Ring T] (FT : ι → τ) (FT_lt : outParam <| ι → τ) [SetLike τ T]
  [IsRingFiltration FT FT_lt]

section FilteredRingHom

class FilteredRingHom extends FilteredHom FR FR_lt FS FS_lt, R →+* S

variable {FR FS FR_lt FS_lt} in
def FilteredRingHom.IsStrict (f : FilteredRingHom FR FR_lt FS FS_lt) : Prop :=
  ∀ p : ι, ∀ y : S, y ∈ f.toFun '' (FR p) ↔ (y ∈ (FS p) ∧ y ∈ f.range)

variable {FR FS FR_lt FS_lt} in
def FilteredRingHom.IsStrict' (f : FilteredRingHom FR FR_lt FS FS_lt) : Prop :=
  ∀ p : ι, ∀ y : S, y ∈ f.toFun '' (FR_lt p) ↔ (y ∈ (FS_lt p) ∧ y ∈ f.range)

variable (g : FilteredRingHom FS FS_lt FT FT_lt) (f : FilteredRingHom FR FR_lt FS FS_lt)

variable {FR FS FT FR_lt FS_lt FT_lt} in
def FilteredRingHom.comp : FilteredRingHom FR FR_lt FT FT_lt := {
    g.toRingHom.comp f.toRingHom with
  pieces_wise := fun i a ha ↦ g.pieces_wise i (f.toFun a) (f.pieces_wise i a ha)
  pieces_wise_lt := fun i a ha ↦ g.pieces_wise_lt i (f.toFun a) (f.pieces_wise_lt i a ha)
}

infixl:100 " ∘ " => FilteredRingHom.comp

end FilteredRingHom

section FilteredModuleHom

variable {R σR : Type*} [Ring R] [SetLike σR R] [AddSubgroupClass σR R] (FR : ι → σR)
  (FR_lt : outParam <| ι → σR) [fil : IsRingFiltration FR FR_lt]

variable {M σM : Type*} [AddCommMonoid M] [Module R M] [SetLike σM M] (FM : ι → σM)
  [AddSubmonoidClass σM M] [SMulMemClass σM R M] (FM_lt : outParam <| ι → σM)

variable {N σN : Type*} [AddCommMonoid N] [Module R N] [SetLike σN N] (FN : ι → σN)
  [AddSubmonoidClass σN N] [SMulMemClass σN R N] (FN_lt : outParam <| ι → σN)

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
  rw [← Quotient.eq_iff_equiv] at h
  have : f.toRingHom (- a + b) ∈ (FS_lt i) :=
    f.pieces_wise_lt i (⟨- a + b, QuotientAddGroup.eq.mp h⟩ : FR_lt i) <| QuotientAddGroup.eq.mp h
  rw [map_add, map_neg] at this
  exact QuotientAddGroup.eq.mpr this

open DirectSum in
variable {FR FR_lt FS FS_lt} in
noncomputable def G : (Graded FR FR_lt) → (Graded FS FS_lt) :=
  fun a ↦
    let _ : (i : ι) → (x : GradedPiece FR FR_lt i) → Decidable (x ≠ 0) := fun _ x ↦
      Classical.propDecidable (x ≠ 0)
    mk (fun i ↦ GradedPiece FS FS_lt i) (DFinsupp.support a)
      <| fun i ↦ (Gf f i) (a i)
@[simp]
lemma G.comp : (G g).comp (G f) = G (g ∘ f) := by
  apply (Set.eqOn_univ (G g ∘ G f) (G (g ∘ f))).mp
  sorry

open DirectSum DFinsupp
instance : (G g).comp (G f) = (G (g.comp f)) := by
  let _ : (i : ι) → (x : GradedPiece FS FS_lt i) → Decidable (x ≠ 0) := fun _ x ↦
    Classical.propDecidable (x ≠ 0)
  let _ : (i : ι) → (x : GradedPiece FR FR_lt i) → Decidable (x ≠ 0) := fun _ x ↦
    Classical.propDecidable (x ≠ 0)

  apply (Set.eqOn_univ (G g ∘ G f) (G (g.comp f))).mp
    fun x a ↦ ? x
  apply ext (fun i ↦ GradedPiece FT FT_lt i)
  intro j

  set s := mk (fun i ↦ GradedPiece FS FS_lt i) (support x)
              (fun i ↦ Gf f i (x i)) with hs
  show mk (GradedPiece FT FT_lt) (support s)
          (fun i ↦ Gf g i (s i)) j
     = mk (fun i ↦ GradedPiece FT FT_lt i) (support x)
          (fun i ↦ Gf (g.comp f) i (x i)) j
  by_cases hjx : j ∈ support x
  · rw[mk_apply_of_mem hjx]
    simp
    sorry
  · rw[mk_apply_of_not_mem hjx]
    by_cases hjs : j ∈ support s
    · simp only [Gf, GradedPiece.mk_eq]
      have : (0 : GradedPiece FS FS_lt j) = ⟦0⟧ := rfl
      rw[mk_apply_of_mem hjs, mk_apply_of_not_mem hjx, this, Quotient.lift_mk]
      simp only [ZeroMemClass.coe_zero, map_zero, QuotientAddGroup.eq_zero_iff]
      apply (QuotientAddGroup.eq_zero_iff _).mp rfl
    · exact mk_apply_of_not_mem hjs


end DirectSum

end Def

section exactness

variable {ι R σ : Type*} [DecidableEq ι] [OrderedAddCommMonoid ι]
  [Ring R] [SetLike σ R] [AddSubgroupClass σ R]

variable (L M N : ι → σ) (L_lt M_lt N_lt : outParam <| ι → σ)
  [IsRingFiltration L L_lt] [IsRingFiltration M M_lt] [IsRingFiltration N N_lt]

variable (f : FilteredRingHom L L_lt M M_lt) (g : FilteredRingHom M M_lt N N_lt)

theorem exact_of_exact (strict : FilteredRingHom.IsStrict' f)
    (exact : Function.Exact f.toRingHom g.toRingHom) : Function.Exact (G f) (G g) := by
  have aux1 : ∀ p : ι, ∀ x : M p, (G g) (DirectSum.of p (GradedPiece M M_lt) x)
  have component_exact : ∀ p : ι, ∀ x : M p, (Gf g p) ⟦x⟧ = 0 →
      ∃ y : L p, (Gf f p) ⟦y⟧ = ⟦x⟧ := by
    intro p x noname
    have : ∃ x' : M_lt p, g.toRingHom x = g.toRingHom x' := sorry
    rcases this with ⟨x', geq⟩
    have : ∃ y : L p, f.toRingHom y = x - x' := sorry
    rcases this with ⟨y, feq⟩
    use y
    let _ : (i : ι) → (x : GradedPiece L L_lt i) → Decidable (x ≠ 0) :=
      fun _ x ↦ Classical.propDecidable (x ≠ 0)
    have : ∃ fy : M p, fy = f.toRingHom y :=
      CanLift.prf (f.toRingHom y) <| f.pieces_wise p y <| SetLike.coe_mem y
    rcases this with ⟨fy, huh⟩

    #check Quotient.lift_mk (fun (s : L p)↦ GradedPiece.mk M M_lt ⟨f.toRingHom s, f.pieces_wise p s (SetLike.coe_mem s)⟩) ?_ y

    have : (Gf f p) (Quotient.mk' y) = Quotient.mk' (fy) := by
      unfold Gf
      simp

      sorry
    sorry
  sorry



end exactness
