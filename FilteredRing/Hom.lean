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
  strict : ∀ p : ι, ∀ y : S, y ∈ f.toRingHom '' (FR p) ↔ (y ∈ (FS p) ∧ y ∈ f.range)
  strict_lt : ∀ p : ι, ∀ y : S, y ∈ f.toRingHom '' (FR_lt p) ↔ (y ∈ (FS_lt p) ∧ y ∈ f.range)

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

variable {ι R S T σR σS σT : Type*} [DecidableEq ι]

variable [Ring R] {FR : ι → σR} {FR_lt : outParam <| ι → σR} [SetLike σR R] [AddSubgroupClass σR R]
variable [Ring S] {FS : ι → σS} {FS_lt : outParam <| ι → σS} [SetLike σS S] [AddSubgroupClass σS S]
variable [Ring T] (FT : ι → σT) (FT_lt : outParam <| ι → σT) [SetLike σT T] [AddSubgroupClass σT T]

variable (f : FilteredRingHom FR FR_lt FS FS_lt)

def Gf (i : ι) : GradedPiece FR FR_lt i →+ GradedPiece FS FS_lt i where
  toFun := by
    intro a
    use Quotient.lift (fun (s : FR i) ↦ GradedPiece.mk FS FS_lt
      ⟨f.toRingHom s, f.pieces_wise i s <| SetLike.coe_mem s⟩) (fun a b h ↦ ?_) a
    rw [← Quotient.eq_iff_equiv] at h
    have : f.toRingHom (- a + b) ∈ (FS_lt i) :=
      f.pieces_wise_lt i (⟨- a + b, QuotientAddGroup.eq.mp h⟩ : FR_lt i) <| QuotientAddGroup.eq.mp h
    rw [map_add, map_neg] at this
    exact QuotientAddGroup.eq.mpr this
  map_zero' := by
    have : (0 : GradedPiece FR FR_lt i) = ⟦0⟧ := rfl
    simp only[this, Quotient.lift_mk]
    simp only [ZeroMemClass.coe_zero, map_zero, QuotientAddGroup.eq_zero_iff]
    rfl
  map_add' := sorry


variable (g : FilteredRingHom FS FS_lt FT FT_lt)
omit [DecidableEq ι] in
lemma Gf_comp (x : AssociatedGraded FR FR_lt) : Gf g i (Gf f i (x i)) = Gf (g ∘ f) i (x i) := by
  obtain ⟨a, ha⟩ := Quotient.exists_rep (x i)
  rw [← ha]
  congr

private noncomputable def GAux : (AssociatedGraded FR FR_lt) → (AssociatedGraded FS FS_lt) :=
  fun a ↦ mk (GradedPiece FS FS_lt) (DFinsupp.support a) <| fun i ↦ (Gf f i) (a i)

lemma GAux_apply (x : AssociatedGraded FR FR_lt) (i : ι) : (GAux f x) i = Gf f i (x i) := by
  dsimp only [GAux]
  by_cases ixsupp : i ∈ DFinsupp.support x
  · simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, mk_apply_of_mem ixsupp]
  · simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, mk_apply_of_not_mem ixsupp]
    rw [DFinsupp.not_mem_support_iff.mp ixsupp, map_zero]

noncomputable def G : (AssociatedGraded FR FR_lt) →+ (AssociatedGraded FS FS_lt) where
  toFun := GAux f
  map_zero' := rfl
  map_add' := fun x y ↦ by
    ext i
    simp only [add_apply, GAux_apply, map_add]

theorem G_to_Gf (x : AssociatedGraded FR FR_lt)(i : ι) : (G f x) i = Gf f i (x i) := by
  simp only [G, AddMonoidHom.coe_mk, ZeroHom.coe_mk, GAux_apply]


lemma Gof_eq_piece  (i) (x : GradedPiece FR FR_lt i):
  (Gf f i) x = (G f) (of (GradedPiece FR FR_lt) i x) i:= by
  rw[G_to_Gf]
  congr
  rw[of_eq_same]

lemma Geq0_iff_pieces0 : G f = 0 ↔ ∀ i, (Gf f i) = 0 := by
  constructor
  · intro eq0 i
    apply AddMonoidHom.ext_iff.mpr fun x ↦ ?_
    rw[Gof_eq_piece, eq0]
    simp only [AddMonoidHom.zero_apply, zero_apply, of_eq_same]
  · intro h
    apply AddMonoidHom.ext_iff.mpr fun x ↦ ?_
    apply AssociatedGraded.ext_iff.mpr fun i ↦ ?_
    rw[G_to_Gf, h]
    simp only [AddMonoidHom.zero_apply, zero_apply]

theorem G_comp: (G g) ∘ (G f) = G (g ∘ f) := by
  ext x i
  simp only [G, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Function.comp_apply, GAux_apply]
  exact Gf_comp FT FT_lt f g x

end DirectSum
