import FilteredRing.Hom

variable {R S T σR σS σT : Type*}

variable [Ring R] [SetLike σR R] [AddSubgroupClass σR R]

variable [Ring S] [SetLike σS S] [AddSubgroupClass σS S]

variable [Ring T] [SetLike σT T] [AddSubgroupClass σT T]

variable {FR : ℤ → σR} {FS : ℤ → σS} {FT : ℤ → σT}

variable [IsRingFiltration FS (fun n ↦ FS (n - 1))]
         [IsRingFiltration FT (fun n ↦ FT (n - 1))]

variable (f : FilteredRingHom FR (fun n ↦ FR (n - 1)) FS (fun n ↦ FS (n - 1)))
         (g : FilteredRingHom FS (fun n ↦ FS (n - 1)) FT (fun n ↦ FT (n - 1)))

open DirectSum DFinsupp

omit [AddSubgroupClass σS S] in
lemma step1 (Exhaustive : IsExhaustiveFiltration FS (fun n ↦ FS (n - 1)))
 : ∃ s, s ≥ 0 ∧ (x : S) ∈ FS (p + s) := by
  obtain ⟨s₀, xin⟩ : ∃ s, (x : S) ∈ FS s := by
    apply Set.mem_iUnion.mp
    rw[← IsExhaustiveFiltration.exhaustive (fun n ↦ FS (n - 1)) (F := FS) (A := S)]
    trivial
  rcases lt_or_le p s₀ with ch | ch
  · use s₀ - p
    simp only [ge_iff_le, sub_nonneg, add_sub_cancel, xin, and_true, le_of_lt ch]
  · use 0
    simp only [ge_iff_le, le_refl, add_zero, (IsFiltration.mono ch) xin, and_self]

omit [IsRingFiltration FS fun n ↦ FS (n - 1)] in
lemma step2 (hx : g.toRingHom x = y)(ch : 0 < s)(hy1 : y ∈ FT p) : (Gf g (p + s)) ⟦⟨x, xin⟩⟧ = 0 := by
  simp only [Gf, GradedPiece.mk_eq, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Quotient.lift_mk,
    QuotientAddGroup.eq_zero_iff]
  show (g.toRingHom x) ∈ FT (p + s - 1)
  rw[hx]
  have : y ∈ FT (p + s - 1) := by
    have : FT p ≤ FT (p + s - 1) := by
      apply IsFiltration.mono (F := FT) (F_lt := (fun n ↦ FT (n - 1)))
      linarith
    exact this hy1
  exact this

theorem c (Gexact : Function.Exact (G f) (G g))
(Exhaustive : IsExhaustiveFiltration FS (fun n ↦ FS (n - 1))) :
 ∀ (p : ℤ) (y : T), y ∈ ⇑g.toRingHom '' ↑(FS p) ↔ y ∈ FT p ∧ y ∈ g.toRingHom.range := by
  intro p y
  constructor
  · rintro ⟨x, xin, eq⟩
    rw[← eq]
    exact ⟨g.pieces_wise p x xin, by use x⟩
  · rintro ⟨hy1, ⟨x, hx⟩⟩
    obtain⟨s, sge0, xin⟩ := step1 Exhaustive
    rcases Or.symm (LE.le.gt_or_eq sge0) with ch | ch
    · rw[← hx]
      rw[ch, add_zero] at xin
      exact Set.mem_image_of_mem (⇑g.toRingHom) xin
    · have : (Gf g (p + s)) ⟦⟨x, xin⟩⟧ = 0 := step2 g hx ch hy1
      obtain⟨z, hz⟩ : ∃ z , (Gf f (p + s)) z = ⟦⟨x, xin⟩⟧ := by
        show ⟦⟨x, xin⟩⟧ ∈ (Gf f (p + s)).range
        have s1 : (G g).ker = (G f).range := by
          exact Function.Exact.addMonoidHom_ker_eq Gexact
        have s2 : (Gf g (p + s)).ker = (Gf f (p + s)).range := by
          ext u
          have : (Gf g (p + s)) u = 0 ↔ (G g) (of (GradedPiece FS (fun n ↦ FS (n - 1))) (p + s) u) = 0:= sorry
          have : (G g) (of (GradedPiece FS (fun n ↦ FS (n - 1))) (p + s) u) = 0 ↔
                  (of (GradedPiece FS (fun n ↦ FS (n - 1))) (p + s) u) ∈ (G f).range := sorry
          have : (of (GradedPiece FS (fun n ↦ FS (n - 1))) (p + s) u) ∈ (G f).range ↔
                u ∈ (Gf f (p + s)).range := sorry
          sorry
        rw[← s2]
        exact this
      obtain⟨z, hz⟩ : ∃ z , (Gf f (p + s)) ⟦z⟧ = ⟦⟨x, xin⟩⟧ := sorry
      have : x - f.toRingHom z ∈ FS (p + s - 1) := sorry
      obtain⟨x', hx'⟩ : ∃ x' : FS (p + s - 1), y = g.toRingHom x' := sorry -- calc
      have : ∃ u : FS p, y = g.toRingHom u := by
        -- by induction
        sorry
      sorry
  -- sorry


theorem test (Gexact : Function.Exact (G f) (G g))
(Exhaustive : IsExhaustiveFiltration FS (fun n ↦ FS (n - 1))) : g.IsStrict :=
  ⟨fun p y ↦ c f g Gexact Exhaustive p y, fun p y ↦ c f g Gexact Exhaustive (p - 1) y⟩
