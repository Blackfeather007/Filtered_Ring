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

variable [Ring R] (FR : ι → γ) (FR_lt : outParam <| ι → γ) [SetLike γ R] [AddSubgroupClass γ R]
variable [Ring S] (FS : ι → σ) (FS_lt : outParam <| ι → σ) [SetLike σ S] [AddSubgroupClass σ S]

variable (f : FilteredRingHom FR FR_lt FS FS_lt)

variable [Ring T] (FT : ι → τ) (FT_lt : outParam <| ι → τ) [SetLike τ T] [AddSubgroupClass τ T]
  (f : FilteredRingHom FR FR_lt FS FS_lt) (g : FilteredRingHom FS FS_lt FT FT_lt)

variable {FR FR_lt FS FS_lt} in
private def Gf (i : ι) : GradedPiece FR FR_lt i → GradedPiece FS FS_lt i := by
  intro a
  use Quotient.lift (fun (s : FR i)↦ GradedPiece.mk FS FS_lt
    ⟨f.toRingHom s, f.pieces_wise i s <| SetLike.coe_mem s⟩) (fun a b h ↦ ?_) a
  rw [← Quotient.eq_iff_equiv] at h
  have : f.toRingHom (- a + b) ∈ (FS_lt i) :=
    f.pieces_wise_lt i (⟨- a + b, QuotientAddGroup.eq.mp h⟩ : FR_lt i) <| QuotientAddGroup.eq.mp h
  rw [map_add, map_neg] at this
  exact QuotientAddGroup.eq.mpr this

variable {FR FR_lt FS FS_lt} in
noncomputable def G : (AssociatedGraded FR FR_lt) → (AssociatedGraded FS FS_lt) := fun a ↦
  mk (fun i ↦ GradedPiece FS FS_lt i) (DFinsupp.support a)
    <| fun i ↦ (Gf f i) (a i)

end DirectSum





section GfComp

open DirectSum

variable {ι R S T γ σ τ : Type*}

variable [Ring R] (FR : ι → γ) (FR_lt : outParam <| ι → γ) [SetLike γ R] [AddSubgroupClass γ R]
variable [Ring S] (FS : ι → σ) (FS_lt : outParam <| ι → σ) [SetLike σ S] [AddSubgroupClass σ S]

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

end GfComp



section GComp

open DirectSum DFinsupp

variable {ι R S T γ σ τ : Type*} [DecidableEq ι]

variable [Ring R] (FR : ι → γ) (FR_lt : outParam <| ι → γ) [SetLike γ R] [AddSubgroupClass γ R]
variable [Ring S] (FS : ι → σ) (FS_lt : outParam <| ι → σ) [SetLike σ S] [AddSubgroupClass σ S]

variable (f : FilteredRingHom FR FR_lt FS FS_lt)

lemma mk_eq_Gf: mk (GradedPiece FS FS_lt) (support x) (fun i ↦ Gf f i (x i)) j = Gf f j (x j) := by
  by_cases hjx : j ∈ support x
  · exact mk_apply_of_mem hjx
  · simp only [Gf, GradedPiece.mk_eq, mk_apply_of_not_mem hjx]
    simp only [mem_support_toFun, ne_eq, not_not] at hjx
    have : (0 : GradedPiece FR FR_lt j) = ⟦0⟧ := rfl
    simp only [hjx, this,  Quotient.lift_mk, ZeroMemClass.coe_zero, map_zero, QuotientAddGroup.eq_zero_iff]
    rfl

variable [Ring T] (FT : ι → τ) (FT_lt : outParam <| ι → τ) [SetLike τ T] [AddSubgroupClass τ T]
variable (g : FilteredRingHom FS FS_lt FT FT_lt)

theorem G.comp: (G g) ∘ (G f) = G (g ∘ f) := by
  apply (Set.eqOn_univ (G g ∘ G f) (G (g ∘ f))).mp fun x a ↦ ? x
  ext j
  obtain⟨y, hy⟩ : ∃ y, ⟦y⟧ = x j := Quotient.exists_rep (x j)
  set s := mk (GradedPiece FS FS_lt) (support x) (fun i ↦ Gf f i (x i)) with hs
  show mk (GradedPiece FT FT_lt) (support s) (fun i ↦ Gf g i (s i)) j
     = mk (GradedPiece FT FT_lt) (support x) (fun i ↦ Gf (g ∘ f) i (x i)) j
  rw[mk_eq_Gf FR FR_lt FT FT_lt (g ∘ f),  mk_eq_Gf FS FS_lt FT FT_lt g,
    hs, mk_eq_Gf FR FR_lt FS FS_lt f, Gf.comp]

end GComp




section exactness

variable {ι R σ : Type*} [DecidableEq ι] [OrderedAddCommMonoid ι]
  [Ring R] [SetLike σ R] [AddSubgroupClass σ R]

variable (L M N : ι → σ) (L_lt M_lt N_lt : outParam <| ι → σ)
  [IsRingFiltration L L_lt] [IsRingFiltration M M_lt] [IsRingFiltration N N_lt]

variable (f : FilteredRingHom L L_lt M M_lt) (g : FilteredRingHom M M_lt N N_lt)


set_option maxHeartbeats 0

theorem exact_of_exact (fstrict : FilteredRingHom.IsStrict f) (gstrict : FilteredRingHom.IsStrict g)
    (exact : Function.Exact f.toRingHom g.toRingHom) : Function.Exact (G f) (G g) := by
  intro m
  constructor

  · -- first prove for single component
    have component_exact : ∀ p : ι, ∀ x : M p, (Gf g p) ⟦x⟧ = 0 → ∃ y : L p, (Gf f p) ⟦y⟧ = ⟦x⟧ := by
      intro p x xto0
      obtain⟨x', geq⟩ : ∃ x' : M_lt p, g.toRingHom x = g.toRingHom x' := by
        simp only [Gf, GradedPiece.mk_eq, Quotient.lift_mk, QuotientAddGroup.eq_zero_iff] at xto0
        have := (gstrict.strict_lt p (g.toRingHom x)).2 ⟨xto0, RingHom.mem_range_self g.toRingHom x⟩
        rcases (Set.mem_image _ _ _).1 this with ⟨x', x'Mltp, geq⟩
        use ⟨x', x'Mltp⟩, geq.symm

      obtain⟨y, feq⟩ : ∃ y : L p, f.toRingHom y = x - x' := by
        apply_fun (fun m ↦ m - g.toRingHom x') at geq
        rw [sub_self, ← map_sub] at geq
        obtain ⟨y', hy'⟩ := exact (x - x') |>.1 geq
        replace strictf := fstrict.strict p (x - x') |>.2
        have part1 : x.1 - x' ∈ M p :=
          sub_mem (SetLike.coe_mem x) <| (IsFiltration.lt_le M M_lt p) x'.2
        replace strictf := strictf ⟨part1, ⟨y', hy'⟩⟩
        obtain ⟨y'', hy''⟩ := strictf
        exact ⟨⟨y'', hy''.1⟩, hy''.2⟩

      use y

      have : (Gf f p) ⟦y⟧ = ⟦⟨f.toRingHom y, f.pieces_wise p y (SetLike.coe_mem y)⟩⟧ := by
        simp only [Gf, GradedPiece.mk_eq, Quotient.lift_mk]
      rw [this]

      sorry

    sorry -- glue components together

  · rintro ⟨l, hl⟩
    rw[← hl]
    show ((G g) ∘ (G f)) l = 0
    rw[G.comp L L_lt M M_lt f N N_lt g]
    ext i
    obtain⟨k, hk⟩ : ∃ k, ⟦k⟧ = l i := Quotient.exists_rep (l i)
    show ((DirectSum.mk (GradedPiece N N_lt) (DFinsupp.support l)) fun i ↦ Gf (g ∘ f) i (l i)) i = 0
    rw [mk_eq_Gf L L_lt N N_lt (g ∘ f) (x := l) (j := i), Gf, ← hk, Quotient.lift_mk]
    have : (⟨(g ∘ f).toRingHom k, by apply (g ∘ f).pieces_wise i k <| SetLike.coe_mem k⟩ : N i) = (0 : N i) :=
      ZeroMemClass.coe_eq_zero.mp (Function.Exact.apply_apply_eq_zero exact k)
    rw[this]
    rfl

end exactness
