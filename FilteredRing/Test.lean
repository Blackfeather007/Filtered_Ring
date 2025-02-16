import FilteredRing.Hom

variable {R S T σR σS σT : Type*}

variable [Ring R] [SetLike σR R] [AddSubgroupClass σR R]

variable [Ring S] [SetLike σS S] [AddSubgroupClass σS S]

variable [Ring T] [SetLike σT T] [AddSubgroupClass σT T]

variable {FR : ℤ → σR} {FS : ℤ → σS} {FT : ℤ → σT}

variable [IsRingFiltration FS (fun n ↦ FS (n - 1))]

variable (f : FilteredRingHom FR (fun n ↦ FR (n - 1)) FS (fun n ↦ FS (n - 1)))
         (g : FilteredRingHom FS (fun n ↦ FS (n - 1)) FT (fun n ↦ FT (n - 1)))

open DirectSum DFinsupp


theorem test (Gexact : Function.Exact (G f) (G g))
(Exhaustive : IsExhaustiveFiltration FS (fun n ↦ FS (n - 1))) : g.IsStrict := by
  constructor
  · intro p y
    constructor
    · intro hy
      obtain ⟨x, xin, eq⟩ := hy
      constructor
      · rw[← eq]
        apply g.pieces_wise p x xin
      · use x
    · rintro ⟨hy1, hy2⟩
      obtain ⟨x, hx⟩ := hy2
      obtain⟨s, sge0, xin⟩ : ∃ s, s ≥ 0 ∧ (x : S) ∈ FS (p + s) := by
        obtain ⟨s₀, xin⟩ : ∃ s, (x : S) ∈ FS s := by
          apply Set.mem_iUnion.mp
          rw[← IsExhaustiveFiltration.exhaustive (fun n ↦ FS (n - 1)) (F := FS) (A := S)]
          trivial
        rcases lt_or_le p s₀ with ch | ch
        · use s₀ - p
          constructor
          . linarith
          · simp only [add_sub_cancel, xin]
        · use 0
          simp only [ge_iff_le, le_refl, add_zero, (IsFiltration.mono ch) xin, and_self]
      rcases Or.symm (LE.le.gt_or_eq sge0) with ch | ch
      · rw[← hx]
        rw[ch, add_zero] at xin
        exact Set.mem_image_of_mem (⇑g.toRingHom) xin
      · have : (Gf g (p + s)) ⟦⟨x, xin⟩⟧ = 0 := by
          simp only [Gf, GradedPiece.mk_eq, Quotient.lift_mk, QuotientAddGroup.eq_zero_iff]
          show (g.toRingHom x) ∈ FT (p + s - 1)
          rw[hx]
          have : y ∈ FT (p + s - 1) := by

            #check IsFiltration.mono
          -- refine FilteredHom.pieces_wise (p + s - 1) x ?_

          sorry

        sorry
      -- obtain⟨z, hz⟩ : ∃ z : FR (p + s), (Gf f (p + s)) (⟦z⟧) = ⟦⟨x, xin⟩⟧ := sorry
      -- have : x - f.toRingHom z ∈ FS_lt (p + s) := sorry
      -- obtain⟨x', hx'⟩ : ∃ x' : FS_lt (p + s), y = g.toRingHom x' := sorry -- calc
      -- have : ∃ u : FS p, y = g.toRingHom u := by
      --   -- by induction
      --   sorry
  · sorry
