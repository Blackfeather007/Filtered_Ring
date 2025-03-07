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

open DirectSum DFinsupp FilteredRingHom

omit [DecidableEq ι] in
lemma exact_component_of_strict_exact_component (fstrict : f.IsStrict) (gstrict : g.IsStrict)
    (exact : Function.Exact f.toRingHom g.toRingHom) :
    ∀ p : ι, ∀ x : GradedPiece FS FS_lt p, Gr(p)[g] x = 0 → ∃ y : FR p, Gr(p)[f] ⟦y⟧ = x := by
  intro p x₀ xto0
  obtain ⟨x, hx⟩ := Quotient.exists_rep x₀
  rw [← hx] at xto0 ⊢
  obtain ⟨x', geq⟩ : ∃ x' : FS_lt p, g.toRingHom x = g.toRingHom x' := by
    simp
    sorry
    -- simp only [Gf, GradedPiece.mk_eq, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Quotient.lift_mk,
    --   QuotientAddGroup.eq_zero_iff] at xto0
    -- have := (gstrict.strict_lt p (g.toRingHom x)).2 ⟨xto0, RingHom.mem_range_self g.toRingHom x⟩
    -- rcases (Set.mem_image _ _ _).1 this with ⟨x', x'Mltp, geq⟩
    -- use ⟨x', x'Mltp⟩, geq.symm
  obtain ⟨y, feq⟩ : ∃ y : FR p, f.toRingHom y = x - x' := by
    apply_fun (fun m ↦ m - g.toRingHom x') at geq
    rw [sub_self, ← map_sub] at geq
    -- replace strictf := (fstrict.strict p (x.1 - x')).2
    -- have sub_mem_mp : x.1 - x' ∈ FS p := by
    --   apply sub_mem (SetLike.coe_mem x)

    --   sorry
    --   -- refine SetLike.mem_coe.mp ?_
    --   --  <| (IsFiltration.lt_le FS FS_lt p) x'.2
    -- replace strictf := strictf ⟨sub_mem_mp, (exact (x - x')).1 geq⟩
    -- -- obtain ⟨y'', hy''⟩ := strictf
    -- exact ⟨⟨y'', hy''.1⟩, hy''.2⟩
    sorry
  use y
  have : Gr(p)[f] ⟦y⟧ = ⟦⟨f.toRingHom y, FilteredHom.pieces_wise (SetLike.coe_mem y)⟩⟧ := by
    simp only [FilteredAddGroupHom.AssociatedGradedRingHom_lift, RingHom.coe_mk, MonoidHom.coe_mk,
      OneHom.coe_mk]
  simp only [this, feq]
  refine QuotientAddGroup.eq.mpr (AddSubgroup.mem_addSubgroupOf.mpr ?_)
  simp only [AddSubgroup.coe_add, NegMemClass.coe_neg, neg_sub, sub_add_cancel, SetLike.coe_mem]

variable  [hasGMul FR FR_lt] [hasGMul FS FS_lt] [hasGMul FT FT_lt]

theorem exact_of_strict_exact (fstrict : f.IsStrict) (gstrict : g.IsStrict)
    (exact : Function.Exact f.toRingHom g.toRingHom) : Function.Exact Gr[f] Gr[g] := by
  intro m
  constructor
  · intro h
    have (i : ι) : ∃ y, Gr(i)[f] ⟦y⟧ = m i := by
      apply exact_component_of_strict_exact_component f g fstrict gstrict exact i
      have : (Gr[g] m) i = 0 := by rw [h]; rfl
      simpa
    set component_2 := fun (i : support m) ↦
      (⟦Classical.choose (this i)⟧ : GradedPiece FR FR_lt i) with hc
    set s : AssociatedGraded FR FR_lt := DirectSum.mk
      (fun i ↦ GradedPiece FR FR_lt i) (support m) component_2 with hs
    have : Gr[f] s = m := by
      apply AssociatedGraded.ext_iff.mpr
      intro j
      simp only [AssociatedGradedRingHom_apply]
      by_cases nh : j ∈ support m
      · rw[mk_apply_of_mem nh, hc, Classical.choose_spec (this j)]
      · rw[hs, mk_apply_of_not_mem nh, map_zero]
        simp only [mem_support_toFun, ne_eq, not_not] at nh
        rw[nh]
    rw[← this]
    exact Set.mem_range_self s
  · rintro ⟨l, hl⟩
    rw[← hl]
    show (Gr[g].comp Gr[f]) l = 0
    rw[AssociatedGradedRingHom_comp g f]
    ext i
    obtain⟨k, hk⟩ : ∃ k, ⟦k⟧ = l i := Quotient.exists_rep (l i)
    simp only [AssociatedGradedRingHom_apply, DirectSum.zero_apply]
    rw [← hk]
    have : (⟨(g.comp f).toFun k, (g.comp f).pieces_wise <| SetLike.coe_mem k⟩ : FT i) = (0 : FT i) :=
      ZeroMemClass.coe_eq_zero.mp (Function.Exact.apply_apply_eq_zero exact k)
    simp only at this
    simp [this]

end exactness
