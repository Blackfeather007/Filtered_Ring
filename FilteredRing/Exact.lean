import FilteredRing.Test


section exactness

variable {ι R σ : Type*} [DecidableEq ι] [OrderedAddCommMonoid ι]
  [Ring R] [SetLike σ R] [AddSubgroupClass σ R]

variable (L M N : ι → σ) (L_lt M_lt N_lt : outParam <| ι → σ)
  [IsRingFiltration L L_lt] [IsRingFiltration M M_lt] [IsRingFiltration N N_lt]

variable (f : FilteredRingHom L L_lt M M_lt) (g : FilteredRingHom M M_lt N N_lt)


open DirectSum DFinsupp


theorem exact_of_strict_exact (fstrict : f.IsStrict) (gstrict : g.IsStrict)
    (exact : Function.Exact f.toRingHom g.toRingHom) : Function.Exact (G f) (G g) := by
  intro m
  constructor
  · have component_exact : ∀ p : ι, ∀ x : M p, (Gf g p) ⟦x⟧ = 0 → ∃ y : L p, (Gf f p) ⟦y⟧ = ⟦x⟧ := by
      intro p x xto0
      obtain⟨x', geq⟩ : ∃ x' : M_lt p, g.toRingHom x = g.toRingHom x' := by
        simp only [Gf, GradedPiece.mk_eq, Quotient.lift_mk, QuotientAddGroup.eq_zero_iff] at xto0
        have := (gstrict.strict_lt p (g.toRingHom x)).2 ⟨xto0, RingHom.mem_range_self g.toRingHom x⟩
        rcases (Set.mem_image _ _ _).1 this with ⟨x', x'Mltp, geq⟩
        use ⟨x', x'Mltp⟩, geq.symm

      obtain⟨y, feq⟩ : ∃ y : L p, f.toRingHom y = x - x' := by
        apply_fun (fun m ↦ m - g.toRingHom x') at geq
        rw [sub_self, ← map_sub] at geq
        replace strictf := fstrict.strict p (x - x') |>.2
        have sub_mem_mp : x.1 - x' ∈ M p :=
          sub_mem (SetLike.coe_mem x) <| (IsFiltration.lt_le M M_lt p) x'.2
        replace strictf := strictf ⟨sub_mem_mp, (exact (x - x')).1 geq⟩
        obtain ⟨y'', hy''⟩ := strictf
        exact ⟨⟨y'', hy''.1⟩, hy''.2⟩

      use y

      have : (Gf f p) ⟦y⟧ = ⟦⟨f.toRingHom y, f.pieces_wise p y (SetLike.coe_mem y)⟩⟧ := by
        simp only [Gf, GradedPiece.mk_eq, Quotient.lift_mk]
      simp only [this, feq]
      refine QuotientAddGroup.eq.mpr (AddSubgroup.mem_addSubgroupOf.mpr ?_)
      simp only [AddSubgroup.coe_add, NegMemClass.coe_neg, neg_sub, sub_add_cancel, SetLike.coe_mem]

    intro h
    have h (i : ι): Gf g i (m i) = 0:= by
      have : ((DirectSum.mk (GradedPiece N N_lt) (DFinsupp.support m)) fun i ↦ Gf g i (m ↑i)) i = 0 :=
        (AddSemiconjBy.eq_zero_iff (((DirectSum.mk (GradedPiece N N_lt) <| DFinsupp.support m) fun i ↦ Gf g i (m ↑i)) i)
        (congrArg (HAdd.hAdd (((DirectSum.mk (fun i ↦ GradedPiece N N_lt i) <| DFinsupp.support m) fun i ↦ Gf g i (m ↑i)) i))
          (congrFun (congrArg DFunLike.coe <| id <| Eq.symm h) i))).mp rfl
      rw [mk_eq_Gf M M_lt N N_lt g (x := m) (j := i)] at this
      exact this

    let component_1 := fun (i : ι) ↦ (if i ∈ support m then Classical.choose (Quotient.exists_rep (m i)) else 0)
    have component_1_prop : ∀ i, ⟦component_1 i⟧ = m i := by
      intro i
      by_cases nh : i ∈ support m
      · have : component_1 i = Classical.choose (Quotient.exists_rep (m i)) := if_pos nh
        rw[this, Classical.choose_spec (Quotient.exists_rep (m i))]
      · have : component_1 i = 0 := if_neg nh
        simp only [mem_support_toFun, ne_eq, not_not] at nh
        rw[this, nh]
        rfl

    have h : ∀ i, Gf g i ⟦component_1 i⟧ = 0 := by
      intro i
      rw[component_1_prop i, h i]

    have tt (i : ι) : ∃ y, Gf f i ⟦y⟧ = m i := by
      rw[← component_1_prop i]
      exact component_exact i (component_1 i) (h i)

    let component_2 := fun (i : support m) ↦ (⟦Classical.choose (tt i)⟧ : GradedPiece L L_lt i) --()
    have (i : support m) :=  Gf f i (component_2 i)
    have (i : support m): Gf f i (component_2 i) = m i := by
      sorry
      -- by_cases nh : i ∈ support m
      -- · have : component_2 i = Classical.choose (tt i) := if_pos nh
      --   rw[this, Classical.choose_spec (tt i)]
      -- · have : component_2 i = 0 := if_neg nh
      --   simp only [mem_support_toFun, ne_eq, not_not] at nh
      --   rw[this, nh, Gf.mk L L_lt M M_lt f i 0]
      --   simp only [Quotient.lift_mk, ZeroMemClass.coe_zero, map_zero, QuotientAddGroup.eq_zero_iff]
      --   exact zero_mem (M_lt i)
    let component_3 := fun (i : ι ) ↦ (if i ∈ support m then (⟦Classical.choose (tt i)⟧ : GradedPiece L L_lt i) else ⟦0⟧)

    set s : AssociatedGraded L L_lt := DirectSum.mk (fun i ↦ GradedPiece L L_lt i) (support m) component_2 with hs

    #check G f
    -- have : s ∈  := sorry
    have (i : support m): (G f) s i = m i := by

      -- refine AssociatedGraded.ext_iff.mpr ?_
      -- intro i
      rw[← this i]
      simp[G]
      show ((DirectSum.mk (GradedPiece M M_lt) (support s)) fun i ↦ Gf f (↑i) (s ↑i)) ↑i = Gf f (↑i) (component_2 i)
      #check mk_eq_Gf L L_lt M M_lt f (j := i) (x := s)
      rw[ mk_eq_Gf L L_lt M M_lt f (j := i) (x := s)]
      congr
      rw[hs]
      show ((DirectSum.mk (GradedPiece L L_lt) (support m)) component_2) i = component_2 i
      #check mk_eq_Gf
      -- rw?
      -- rw[  L L_lt M M_lt f (j := i) (x := component_2)]
      -- #check
      -- rw[]
      -- refine Eq.symm ((fun {ι} α [(i : ι) → Zero (α i)] {f} {i} {a} ↦ mem_singleton_apply_iff.mp) ?_)
      sorry
    -- #check mk _ component_2
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
