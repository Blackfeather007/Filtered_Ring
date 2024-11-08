import FilteredRing.Basic

universe u

suppress_compilation

set_option linter.unusedSectionVars false

set_option maxHeartbeats 0

variable {R : Type u} [Ring R]

variable {ι : Type v} [OrderedCancelAddCommMonoid ι] [DecidableEq ι]

variable (F : ι → AddSubgroup R) [FilteredRing F]

def F_lt (i : ι) := ⨆ k < i, F k

abbrev GradedPiece (i : ι) := F i ⧸ (F_lt F i).comap (F i).subtype

def GradedPiece' (i : ι) := (DirectSum.of (GradedPiece F) i).range

variable {F} in
lemma Filtration.flt_mul_mem {i j : ι} {x y} (hx : x ∈ F_lt F i) (hy : y ∈ F j) :
    x * y ∈ F_lt F (i + j) := by
  rw [F_lt, iSup_subtype'] at hx ⊢
  induction hx using AddSubgroup.iSup_induction' with
  | hp i x hx =>
    exact AddSubgroup.mem_iSup_of_mem ⟨i + j, add_lt_add_right i.2 _⟩ (FilteredRing.mul_mem hx hy)
  | h1 =>
    rw [zero_mul]
    exact zero_mem _
  | hmul _ _ _ _ ih₁ ih₂ =>
    rw [add_mul]
    exact add_mem ih₁ ih₂

variable {F} in
lemma Filtration.mul_flt_mem {i j : ι} {x y} (hx : x ∈ F i) (hy : y ∈ F_lt F j) :
    x * y ∈ F_lt F (i + j) := by
  rw [F_lt, iSup_subtype'] at hy ⊢
  induction hy using AddSubgroup.iSup_induction' with
  | hp j y hy =>
    exact AddSubgroup.mem_iSup_of_mem ⟨i + j, add_lt_add_left j.2 _⟩ (FilteredRing.mul_mem hx hy)
  | h1 =>
    rw [mul_zero]
    exact zero_mem _
  | hmul _ _ _ _ ih₁ ih₂ =>
    rw [mul_add]
    exact add_mem ih₁ ih₂

def gradedMul {i j : ι} : GradedPiece F i → GradedPiece F j → GradedPiece F (i + j) := by
  intro x y
  refine Quotient.map₂' (fun x y ↦ ⟨x.1 * y.1, FilteredRing.mul_mem x.2 y.2⟩)
    ?_ x y
  intro x₁ x₂ hx y₁ y₂ hy
  simp [QuotientAddGroup.leftRel_apply, AddSubgroup.mem_addSubgroupOf] at hx hy ⊢
  have eq : - (x₁.1 * y₁) + x₂ * y₂ = (- x₁ + x₂) * y₁ + x₂ * (- y₁ + y₂) := by noncomm_ring
  rw [eq]
  exact add_mem (Filtration.flt_mul_mem hx y₁.2) (Filtration.mul_flt_mem x₂.2 hy)

#check eqRec_heq
#check Eq.recOn
set_option pp.proofs true in
instance : DirectSum.GSemiring (GradedPiece F) where
  mul := gradedMul F
  mul_zero := by
    intro i j a
    rw [← QuotientAddGroup.mk_zero, ← QuotientAddGroup.mk_zero]
    induction a using Quotient.ind'
    change Quotient.mk'' _ = Quotient.mk'' _
    rw [Quotient.eq'']
    simp only [ZeroMemClass.coe_zero, mul_zero,
      QuotientAddGroup.leftRel_apply, add_zero, neg_mem_iff]
    exact zero_mem _
  zero_mul := by
    intro i j a
    rw [← QuotientAddGroup.mk_zero, ← QuotientAddGroup.mk_zero]
    induction a using Quotient.ind'
    change Quotient.mk'' _ = Quotient.mk'' _
    rw [Quotient.eq'']
    simp only [ZeroMemClass.coe_zero, zero_mul,
      QuotientAddGroup.leftRel_apply, add_zero, neg_mem_iff]
    exact zero_mem _
  mul_add := by
    intro i j a b c
    induction a using Quotient.ind'
    induction b using Quotient.ind'
    induction c using Quotient.ind'
    change Quotient.mk'' _ = Quotient.mk'' _
    rw [Quotient.eq'']
    simp [QuotientAddGroup.leftRel_apply, AddSubgroup.mem_addSubgroupOf]
    rw [mul_add, neg_add_eq_zero.mpr]
    exact zero_mem _
    rfl
  add_mul := by
    intro i j a b c
    induction a using Quotient.ind'
    induction b using Quotient.ind'
    induction c using Quotient.ind'
    change Quotient.mk'' _ = Quotient.mk'' _
    rw [Quotient.eq'']
    simp [QuotientAddGroup.leftRel_apply, AddSubgroup.mem_addSubgroupOf]
    rw [add_mul, neg_add_eq_zero.mpr]
    exact zero_mem _
    rfl
  one := Quotient.mk'' ⟨1, FilteredRing.one⟩
  one_mul := by
    intro ⟨i, a⟩
    apply Sigma.ext
    · simp only [GradedMonoid.fst_mul, GradedMonoid.fst_one, zero_add]
    simp only [QuotientAddGroup.mk_zero, id_eq, ZeroMemClass.coe_zero,
      eq_mpr_eq_cast, cast_eq, AddSubgroup.coe_add, AddMemClass.mk_add_mk, NegMemClass.coe_neg,
      GradedMonoid.fst_mul, GradedMonoid.fst_one, GradedMonoid.snd_mul, GradedMonoid.snd_one]
    unfold gradedMul
    generalize_proofs h1 h2 h3
    set ll : GradedPiece F i = GradedPiece F (0 + i) := congrArg (GradedPiece F) (zero_add i).symm with hl
    have heq : HEq (ll ▸ a) a := by aesop
    refine HEq.trans ?_ heq
    apply heq_of_eq
    induction a using Quotient.ind'
    rename_i a
    dsimp only [Quotient.map₂'_mk'', one_mul]
    convert_to Quotient.mk'' _ = Quotient.mk'' _
    swap
    exact (zero_add i).symm ▸ a
    · rw [hl]
      let e := (zero_add i).symm
      generalize (zero_add i).symm = e
      revert e
      generalize 0 + i = j
      apply Eq.rec
      rfl
    rw [Quotient.eq'']
    simp only [zero_add, AddSubgroup.comap_subtype, one_mul, QuotientAddGroup.leftRel_apply, AddSubgroup.mem_addSubgroupOf]
    convert_to 0 ∈ F_lt F i
    · simp only [AddSubgroup.coe_add, NegMemClass.coe_neg, neg_add_cancel]
      have : (Eq.symm (zero_add i) ▸ a).1 = a.1 := by
        congr!
        exact zero_add i
        apply eqRec_heq (Eq.symm (zero_add i))
      rw [this]
      simp only [neg_add_cancel]
    exact zero_mem _
  mul_one := sorry
  mul_assoc := by
    intro ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩
    refine Sigma.ext (add_assoc i j k) (eqRec_heq ?_ ?_)
    apply Sigma.ext (add_assoc i j k)
    simp only [QuotientAddGroup.mk_zero, id_eq, ZeroMemClass.coe_zero,
      eq_mpr_eq_cast, cast_eq, AddSubgroup.coe_add, AddMemClass.mk_add_mk, NegMemClass.coe_neg,
      GradedMonoid.fst_mul, GradedMonoid.snd_mul]
    unfold gradedMul
    simp

    sorry
  gnpow := fun n i x => Quotient.mk'' ⟨x.out'.1 ^ n, by
    induction' n with d hd
    · simpa [zero_smul, pow_zero] using FilteredRing.one
    simpa [pow_succ, succ_nsmul] using FilteredRing.mul_mem hd x.out'.2⟩
  gnpow_zero' := fun ⟨i, a⟩ => by
    have e := by show (0 • i) = 0; simp only [pow_zero, zero_smul]
    refine Sigma.eq e ?_
    simp only [GradedMonoid.fst_one, id_eq, eq_mpr_eq_cast, Nat.recAux_zero, GradedMonoid.snd_one]
    -- show Quotient.mk'' _ = Quotient.mk'' _
    generalize_proofs h1 h2
    have h2' : 1 ∈ F (0 • i) := by simpa [zero_smul] using h2
    rw [Eq.rec_eq_cast]
    refine cast_eq_iff_heq.mpr ?_
    -- #check e ▸ (Quotient.mk'' (⟨(Quotient.out' a) ^ 0, h1⟩ : (F (0 • i))))
    -- convert_to e ▸ (Quotient.mk'' (⟨(Quotient.out' a) ^ 0, h1⟩ : (F (0 • i)))) = Quotient.mk'' ⟨1, h2'⟩
    -- show e ▸ (Quotient.mk'' ⟨↑(Quotient.out' a) ^ 0, h1⟩) = Quotient.mk'' ⟨1, h2⟩

    sorry
  gnpow_succ' := fun n ⟨i, a⟩ => by
    -- refine Sigma.eq
    --   (by show (n + 1) • i = n • i + i; simp only [Nat.succ_eq_add_one,succ_nsmul]) ?_
    apply sigma_mk_injective
    generalize_proofs h1 h2
    simp only [Nat.succ_eq_add_one]


    sorry
  natCast := fun n => Quotient.mk'' (n • (⟨1, FilteredRing.one⟩ : F 0))
  natCast_zero := by simp only [zero_smul, QuotientAddGroup.mk_zero]
  natCast_succ := by
    intro n
    simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    apply Quotient.eq''.mpr
    convert_to Setoid.r (((n : F 0) + 1) * 1) ((n : F 0) * 1 + 1)
    rw [mul_one, mul_one]
    simp only [QuotientAddGroup.leftRel_apply, neg_add_cancel ((n : F 0) + 1)]
    exact zero_mem _
