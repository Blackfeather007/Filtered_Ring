import FilteredRing.Hom
import FilteredRing.Filtration_to_Grading

section exactness

variable {ι R S T σR σS σT : Type*} [DecidableEq ι] [OrderedAddCommMonoid ι]

variable [Ring R] [SetLike σR R] [AddSubgroupClass σR R]

variable [Ring S] [SetLike σS S] [AddSubgroupClass σS S]

variable [Ring T] [SetLike σT T] [AddSubgroupClass σT T]

variable {FR : ι → σR} {FS : ι → σS} {FT : ι → σT}

variable {FR_lt: outParam <| ι → σR} {FS_lt: outParam <| ι → σS} {FT_lt: outParam <| ι → σT}

variable [IsRingFiltration FS FS_lt] -- [IsRingFiltration FR FR_lt] [IsRingFiltration FT FT_lt]

variable (f : FilteredRingHom FR FR_lt FS FS_lt) (g : FilteredRingHom FS FS_lt FT FT_lt)

open DirectSum DFinsupp

omit [DecidableEq ι] in
lemma exact_component_of_strict_exact_component (fstrict : f.IsStrict) (gstrict : g.IsStrict)
    (exact : Function.Exact f.toRingHom g.toRingHom) :
    ∀ p : ι, ∀ x : GradedPiece FS FS_lt p, (Gf g p) x = 0 → ∃ y : FR p, (Gf f p) ⟦y⟧ = x := by
  intro p x₀ xto0
  obtain ⟨x, hx⟩ := Quotient.exists_rep x₀
  rw [← hx] at xto0 ⊢
  obtain ⟨x', geq⟩ : ∃ x' : FS_lt p, g.toRingHom x = g.toRingHom x' := by
    simp only [Gf, GradedPiece.mk_eq, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Quotient.lift_mk,
      QuotientAddGroup.eq_zero_iff] at xto0
    have := (gstrict.strict_lt p (g.toRingHom x)).2 ⟨xto0, RingHom.mem_range_self g.toRingHom x⟩
    rcases (Set.mem_image _ _ _).1 this with ⟨x', x'Mltp, geq⟩
    use ⟨x', x'Mltp⟩, geq.symm
  obtain ⟨y, feq⟩ : ∃ y : FR p, f.toRingHom y = x - x' := by
    apply_fun (fun m ↦ m - g.toRingHom x') at geq
    rw [sub_self, ← map_sub] at geq
    replace strictf := fstrict.strict p (x - x') |>.2
    have sub_mem_mp : x.1 - x' ∈ FS p :=
      sub_mem (SetLike.coe_mem x) <| (IsFiltration.lt_le FS FS_lt p) x'.2
    replace strictf := strictf ⟨sub_mem_mp, (exact (x - x')).1 geq⟩
    obtain ⟨y'', hy''⟩ := strictf
    exact ⟨⟨y'', hy''.1⟩, hy''.2⟩
  use y
  have : (Gf f p) ⟦y⟧ = ⟦⟨f.toRingHom y, f.pieces_wise p y (SetLike.coe_mem y)⟩⟧ := by
    simp only [Gf, GradedPiece.mk_eq, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Quotient.lift_mk]
  simp only [this, feq]
  refine QuotientAddGroup.eq.mpr (AddSubgroup.mem_addSubgroupOf.mpr ?_)
  simp only [AddSubgroup.coe_add, NegMemClass.coe_neg, neg_sub, sub_add_cancel, SetLike.coe_mem]

theorem exact_of_strict_exact (fstrict : f.IsStrict) (gstrict : g.IsStrict)
    (exact : Function.Exact f.toRingHom g.toRingHom) : Function.Exact (G f) (G g) := by
  intro m
  constructor
  · intro h
    have tt (i : ι) : ∃ y, Gf f i ⟦y⟧ = m i := by
      apply exact_component_of_strict_exact_component f g fstrict gstrict exact i
      have : (G g m) i = 0 := by rw [h]; rfl
      simp only [G, AddMonoidHom.coe_mk, ZeroHom.coe_mk, GAux_apply] at this
      exact this
    set component_2 := fun (i : support m) ↦ (⟦Classical.choose (tt i)⟧ : GradedPiece FR FR_lt i) with hc
    set s : AssociatedGraded FR FR_lt := DirectSum.mk (fun i ↦ GradedPiece FR FR_lt i) (support m) component_2 with hs
    have : (G f) s = m := by
      apply AssociatedGraded.ext_iff.mpr
      intro j
      simp only [G, AddMonoidHom.coe_mk, ZeroHom.coe_mk, GAux_apply]
      by_cases nh : j ∈ support m
      · rw[mk_apply_of_mem nh, hc, Classical.choose_spec (tt j)]
      · rw[hs, mk_apply_of_not_mem nh, map_zero]
        simp only [mem_support_toFun, ne_eq, not_not] at nh
        rw[nh]
    rw[← this]
    exact Set.mem_range_self s
  · rintro ⟨l, hl⟩
    rw[← hl]
    show ((G g) ∘ (G f)) l = 0
    rw[G_comp FT FT_lt f g]
    ext i
    obtain⟨k, hk⟩ : ∃ k, ⟦k⟧ = l i := Quotient.exists_rep (l i)
    simp only [G, AddMonoidHom.coe_mk, ZeroHom.coe_mk, GAux_apply, Gf, RingHom.coe_mk,
      MonoidHom.coe_mk, OneHom.coe_mk, GradedPiece.mk_eq, DirectSum.zero_apply]
    rw [← hk, Quotient.lift_mk]
    have : (⟨(g ∘ f).toRingHom k, by apply (g ∘ f).pieces_wise i k <| SetLike.coe_mem k⟩ : FT i) = (0 : FT i) :=
      ZeroMemClass.coe_eq_zero.mp (Function.Exact.apply_apply_eq_zero exact k)
    simp at this
    simp only [this, QuotientAddGroup.mk_zero]

end exactness
