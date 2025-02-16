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




section FilteredRingHom

variable {ι R S T γ σ τ : Type*} [OrderedAddCommMonoid ι]

variable [Ring R] (FR : ι → γ) (FR_lt : outParam <| ι → γ) [SetLike γ R] [IsRingFiltration FR FR_lt]
variable [Ring S] (FS : ι → σ) (FS_lt : outParam <| ι → σ) [SetLike σ S] [IsRingFiltration FS FS_lt]
variable [Ring T] (FT : ι → τ) (FT_lt : outParam <| ι → τ) [SetLike τ T] [IsRingFiltration FT FT_lt]

class FilteredRingHom extends FilteredHom FR FR_lt FS FS_lt, R →+* S

variable {FR FS FR_lt FS_lt} in
class FilteredRingHom.IsStrict (f : outParam <| FilteredRingHom FR FR_lt FS FS_lt) : Prop where
  strict : ∀ p : ι, ∀ y : S, y ∈ f.toFun '' (FR p) ↔ (y ∈ (FS p) ∧ y ∈ f.range)
  strict_lt : ∀ p : ι, ∀ y : S, y ∈ f.toFun '' (FR_lt p) ↔ (y ∈ (FS_lt p) ∧ y ∈ f.range)

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

variable {ι : Type*} [OrderedAddCommMonoid ι]

variable {R σR : Type*} [Ring R] [SetLike σR R] [AddSubgroupClass σR R] (FR : ι → σR)
  (FR_lt : outParam <| ι → σR) [fil : IsRingFiltration FR FR_lt]

variable {M σM : Type*} [AddCommMonoid M] [Module R M] [SetLike σM M] (FM : ι → σM)
  [AddSubmonoidClass σM M] [SMulMemClass σM R M] (FM_lt : outParam <| ι → σM)

variable {N σN : Type*} [AddCommMonoid N] [Module R N] [SetLike σN N] (FN : ι → σN)
  [AddSubmonoidClass σN N] [SMulMemClass σN R N] (FN_lt : outParam <| ι → σN)

class FilteredModuleHom extends FilteredHom FM FM_lt FN FN_lt, M →ₗ[R] N

end FilteredModuleHom




section DirectSum

open DirectSum

variable {ι R S T γ σ τ : Type*} [OrderedAddCommMonoid ι] [DecidableEq ι]

variable [Ring R] {FR : ι → γ} {FR_lt : outParam <| ι → γ} [SetLike γ R] [AddSubgroupClass γ R]
variable [Ring S] {FS : ι → σ} {FS_lt : outParam <| ι → σ} [SetLike σ S] [AddSubgroupClass σ S]

variable (f : FilteredRingHom FR FR_lt FS FS_lt)

variable [Ring T] (FT : ι → τ) (FT_lt : outParam <| ι → τ) [SetLike τ T] [AddSubgroupClass τ T]
  (f : FilteredRingHom FR FR_lt FS FS_lt) (g : FilteredRingHom FS FS_lt FT FT_lt)

def Gf (i : ι) : GradedPiece FR FR_lt i → GradedPiece FS FS_lt i := by
  intro a
  use Quotient.lift (fun (s : FR i)↦ GradedPiece.mk FS FS_lt
    ⟨f.toRingHom s, f.pieces_wise i s <| SetLike.coe_mem s⟩) (fun a b h ↦ ?_) a
  rw [← Quotient.eq_iff_equiv] at h
  have : f.toRingHom (- a + b) ∈ (FS_lt i) :=
    f.pieces_wise_lt i (⟨- a + b, QuotientAddGroup.eq.mp h⟩ : FR_lt i) <| QuotientAddGroup.eq.mp h
  rw [map_add, map_neg] at this
  exact QuotientAddGroup.eq.mpr this

noncomputable def G : (AssociatedGraded FR FR_lt) → (AssociatedGraded FS FS_lt) := fun a ↦
  mk (fun i ↦ GradedPiece FS FS_lt i) (DFinsupp.support a)
    <| fun i ↦ (Gf f i) (a i)

end DirectSum





section GfComp

open DirectSum

variable {ι R S T γ σ τ : Type*}

variable [Ring R] {FR : ι → γ} {FR_lt : outParam <| ι → γ} [SetLike γ R] [AddSubgroupClass γ R]
variable [Ring S] {FS : ι → σ} {FS_lt : outParam <| ι → σ} [SetLike σ S] [AddSubgroupClass σ S]

variable (f : FilteredRingHom FR FR_lt FS FS_lt)

lemma Gf.mk (j : ι) (y : FR j) : Gf f j ⟦y⟧ =
    ⟦(⟨f.toRingHom y, f.toFilteredHom.pieces_wise j y <| SetLike.coe_mem y⟩ : FS j)⟧ := rfl

variable [Ring T] (FT : ι → τ) (FT_lt : outParam <| ι → τ) [SetLike τ T] [AddSubgroupClass τ T]
variable (g : FilteredRingHom FS FS_lt FT FT_lt)

lemma Gf.comp (x : AssociatedGraded FR FR_lt) : Gf g j (Gf f j (x j)) = Gf (g ∘ f) j (x j) := by
  obtain⟨a, ha⟩ := Quotient.exists_rep (x j)
  rw[← ha]
  repeat rw[Gf.mk]
  congr

lemma zero_to_zero : Gf f i 0 = 0 := by
  have : (0 : GradedPiece FR FR_lt i) = ⟦0⟧ := rfl
  simp only [Gf, this,  Quotient.lift_mk, ZeroMemClass.coe_zero, map_zero, QuotientAddGroup.eq_zero_iff]
  rfl

end GfComp



section GComp

open DirectSum DFinsupp

variable {ι R S T γ σ τ : Type*} [DecidableEq ι]

variable [Ring R] {FR : ι → γ} {FR_lt : outParam <| ι → γ} [SetLike γ R] [AddSubgroupClass γ R]
variable [Ring S] {FS : ι → σ} {FS_lt : outParam <| ι → σ} [SetLike σ S] [AddSubgroupClass σ S]

variable (f : FilteredRingHom FR FR_lt FS FS_lt)

variable [Ring T] {FT : ι → τ} {FT_lt : outParam <| ι → τ} [SetLike τ T] [AddSubgroupClass τ T]
variable (g : FilteredRingHom FS FS_lt FT FT_lt)

theorem G_to_Gf (x : AssociatedGraded FR FR_lt)(i : ι) : (G f x) i = Gf f i (x i) := by
  dsimp only[G]
  by_cases hjx : i ∈ support x
  · exact mk_apply_of_mem hjx
  · simp only [GradedPiece.mk_eq, mk_apply_of_not_mem hjx]
    simp only [mem_support_toFun, ne_eq, not_not] at hjx
    rw[hjx, ← zero_to_zero f]

theorem G.comp: (G g) ∘ (G f) = G (g ∘ f) := by
  apply (Set.eqOn_univ (G g ∘ G f) (G (g ∘ f))).mp fun x a ↦ ? x
  ext j
  show G g (G f x) j = (G (g ∘ f) x) j
  repeat rw[G_to_Gf]
  exact Gf.comp f FT FT_lt g x

end GComp
