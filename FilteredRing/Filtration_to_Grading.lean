import FilteredRing.Basic

universe u

set_option maxHeartbeats 0

variable {ι : Type v} [OrderedCancelAddCommMonoid ι]

section GeneralGraded

variable {A : Type u} [AddCommGroup A] {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]

variable (F : ι → σ) (F_lt : outParam <| ι → σ) [IsFiltration F F_lt]

instance [IsFiltration F F_lt] (i : ι) : Setoid (AddSubgroupClass.subtype (F i)).range :=
  QuotientAddGroup.leftRel ((AddSubgroupClass.subtype (F_lt i)).range.addSubgroupOf (AddSubgroupClass.subtype (F i)).range)

abbrev GradedPiece (i : ι) := (AddSubgroupClass.subtype (F i)).range ⧸
    (AddSubgroupClass.subtype (F_lt i)).range.addSubgroupOf (AddSubgroupClass.subtype (F i)).range

end GeneralGraded

section

instance {R : Type u} [Ring R] {σ : Type*} [SetLike σ R] [AddSubgroupClass σ R]
    (F : ι → σ) (F_lt : outParam <| ι → σ) [IsRingFiltration F F_lt]: One (GradedPiece F F_lt 0)  where
  one := ⟦⟨1, AddMonoidHom.mem_range.mpr (by use 1; rfl)⟩⟧

end

section GradedRing

variable {R : Type u} [Ring R] {σ : Type*} [SetLike σ R] [AddSubgroupClass σ R]

variable (F : ι → σ) (F_lt : outParam <| ι → σ)

section HasGMul

class hasGMul extends IsRingFiltration F F_lt : Prop where
  F_lt_mul_mem {i j : ι} {x y} : x ∈ F_lt i → y ∈ F j → x * y ∈ F_lt (i + j)
  mul_F_lt_mem {i j : ι} {x y} : x ∈ F i → y ∈ F_lt j → x * y ∈ F_lt (i + j)

instance (F : ℤ → σ) (mono : ∀ {a b : ℤ}, a ≤ b → F a ≤ F b) (one_mem : 1 ∈ F 0)
  (mul_mem : ∀ {i j x y}, x ∈ F i → y ∈ F j → x * y ∈ F (i + j)) : hasGMul F (fun n ↦ F (n - 1)) := {
    instIsRingFiltrationIntHSubOfNat F mono one_mem mul_mem with
    F_lt_mul_mem := fun h1 h2 ↦ by
      have := mul_mem h1 h2
      rwa [sub_add_eq_add_sub] at this
    mul_F_lt_mem := fun h1 h2 ↦ by
      have := mul_mem h1 h2
      rwa [add_sub_assoc'] at this }

instance (F : ι → AddSubgroup R) (F_lt : outParam <| ι → AddSubgroup R) [IsRingFiltration F F_lt] :
    hasGMul F F_lt where
  F_lt_mul_mem := by
    intro i j x y hx hy
    let S : AddSubgroup R := {
      carrier := {z | z * y ∈ F_lt (i + j)}
      add_mem' := fun ha hb ↦ by simp only [Set.mem_setOf_eq, add_mul, add_mem ha.out hb.out]
      zero_mem' := by simp only [Set.mem_setOf_eq, zero_mul, zero_mem]
      neg_mem' := by simp only [Set.mem_setOf_eq, neg_mul, neg_mem_iff, imp_self, implies_true]}
    exact IsRingFiltration.toIsFiltration.is_sup S i
      (fun k hk z hz ↦ IsFiltration.is_le (add_lt_add_right  hk j) (IsRingFiltration.mul_mem hz hy)) hx
  mul_F_lt_mem := by
    intro i j x y hx hy
    let S : AddSubgroup R := {
      carrier := {z | x * z ∈ F_lt (i + j)}
      add_mem' := fun ha hb ↦ by simp only [Set.mem_setOf_eq, mul_add, add_mem ha.out hb.out]
      zero_mem' := by simp only [Set.mem_setOf_eq, mul_zero, zero_mem]
      neg_mem' := by simp only [Set.mem_setOf_eq, mul_neg, neg_mem_iff, imp_self, implies_true]}
    exact IsRingFiltration.toIsFiltration.is_sup S j
      (fun k hk z hz ↦ IsFiltration.is_le (add_lt_add_left hk i) (IsRingFiltration.mul_mem hx hz)) hy

def Filtration.hMul [IsRingFiltration F F_lt] (i j : ι) (x : (AddSubgroupClass.subtype (F i)).range) (y : (AddSubgroupClass.subtype (F j)).range) : (AddSubgroupClass.subtype (F (i + j))).range where
  val := x * y
  property := by
    rcases x.2 with ⟨x', hx'⟩
    rcases y.2 with ⟨y', hy'⟩
    simp [← hx', ← hy', IsRingFiltration.mul_mem x'.2 y'.2]

instance [IsRingFiltration F F_lt] : HMul (AddSubgroupClass.subtype (F i)).range (AddSubgroupClass.subtype (F j)).range (AddSubgroupClass.subtype (F (i + j))).range where
  hMul := Filtration.hMul F F_lt i j

theorem Filtration.mul_equiv_mul [hasGMul F F_lt] ⦃x₁ x₂ : (AddSubgroupClass.subtype (F i)).range⦄ (hx : x₁ ≈ x₂) ⦃y₁ y₂ : (AddSubgroupClass.subtype (F j)).range⦄ (hy : y₁ ≈ y₂) :
    x₁ * y₁ ≈ x₂ * y₂ := by
  simp [HasEquiv.Equiv, QuotientAddGroup.leftRel_apply, AddSubgroup.mem_addSubgroupOf, AddSubgroup.comap] at hx hy ⊢
  have eq : - ((x₁ * y₁) : (AddSubgroupClass.subtype (F (i + j))).range).1 + ((x₂ * y₂) : (AddSubgroupClass.subtype (F (i + j))).range).1 = (- x₁ + x₂) * y₁ + x₂ * (- y₁ + y₂) := by noncomm_ring
  rw [eq]
  rcases y₁.2 with ⟨y₁', hy₁'⟩
  rcases x₂.2 with ⟨x₂', hx₂'⟩
  exact add_mem (hasGMul.F_lt_mul_mem (F := F) hx (by simp [← hy₁'])) (hasGMul.mul_F_lt_mem (F := F) (by simp [← hx₂']) hy)

variable [hasGMul F F_lt]

def gradedMul {i j : ι} (x : GradedPiece F F_lt i) (y : GradedPiece F F_lt j) : GradedPiece F F_lt (i + j) :=
  Quotient.map₂ (· * ·) (Filtration.mul_equiv_mul F F_lt) x y

instance hMul {i j : ι} :
    HMul (GradedPiece F F_lt i) (GradedPiece F F_lt j) (GradedPiece F F_lt (i + j)) where
  hMul := gradedMul F F_lt

namespace GradedPiece

def mk {i : ι} (x : (AddSubgroupClass.subtype (F i)).range) : GradedPiece F F_lt i := ⟦x⟧

omit [OrderedCancelAddCommMonoid ι] in
@[simp]
lemma mk_congr {i : ι} (x y : (AddSubgroupClass.subtype (F i)).range) (h : x = y) : mk F F_lt x = mk F F_lt y := congrArg (mk F F_lt) h

@[simp]
lemma sound {i : ι} (x y : (AddSubgroupClass.subtype (F i)).range) : x ≈ y → mk F F_lt x = mk F F_lt y := Quotient.sound

@[simp]
lemma exact {i : ι} (x y : (AddSubgroupClass.subtype (F i)).range) : mk F F_lt x = mk F F_lt y → x ≈ y := Quotient.exact

section HEq

lemma GradedPiece.mk_mul {i j : ι} (x : (AddSubgroupClass.subtype (F i)).range) (y : (AddSubgroupClass.subtype (F j)).range) : mk F F_lt x * mk F F_lt y = mk F F_lt (x * y) := rfl

section

omit [OrderedCancelAddCommMonoid ι] [hasGMul F F_lt]

@[simp]
lemma mk_eq {i : ι} (x : (AddSubgroupClass.subtype (F i)).range) : mk F F_lt x = ⟦x⟧ := rfl

lemma GradedPiece.mk_zero {i : ι} : mk F F_lt 0  = (0 : GradedPiece F F_lt i) := rfl

lemma HEq_rfl {i j : ι} {r : R} (h : i = j)
    (hi : r ∈ (AddSubgroupClass.subtype (F i)).range) (hj : r ∈ (AddSubgroupClass.subtype (F j)).range) :
    HEq (mk F F_lt ⟨r, hi⟩) (mk F F_lt ⟨r, hj⟩) :=
  h ▸ HEq.rfl

theorem HEq_eq_mk_eq {i j : ι} {x : GradedPiece F F_lt i} {y : GradedPiece F F_lt j} {r s : R}
    (h : i = j) (e : r = s) (hi : r ∈ (AddSubgroupClass.subtype (F i)).range) (hj : s ∈ (AddSubgroupClass.subtype (F j)).range)
    (hx : x = mk F F_lt ⟨r, hi⟩) (hy : y = mk F F_lt ⟨s, hj⟩) : HEq x y := by
  rw [hx, hy]
  subst e
  exact HEq_rfl F F_lt h hi hj

-- Will be easier to use if HMul intances for F i is added and some other refactor is done.
theorem HEq_eq_mk_coe_eq {i j : ι} {x : GradedPiece F F_lt i} {y : GradedPiece F F_lt j}
    (r : (AddSubgroupClass.subtype (F i)).range) (s : (AddSubgroupClass.subtype (F j)).range)
    (h : i = j) (e : (r : R) = (s : R)) (hx : x = mk F F_lt r) (hy : y = mk F F_lt s) : HEq x y :=
  HEq_eq_mk_eq F F_lt h e r.2 (e ▸ s.2) hx hy

end

lemma gradedMul_def {i j : ι} (x : (AddSubgroupClass.subtype (F i)).range) (y : (AddSubgroupClass.subtype (F j)).range) :
  mk F F_lt (Filtration.hMul F F_lt i j x y) = gradedMul F F_lt (mk F F_lt x) (mk F F_lt y) := rfl

end HEq

end GradedPiece

namespace GradedMul

open GradedPiece

instance : GradedMonoid.GMul (GradedPiece F F_lt) where
  mul := gradedMul F F_lt

instance : GradedMonoid.GOne (GradedPiece F F_lt) where
  one := (1 : GradedPiece F F_lt 0)

variable {F} in
theorem GradedPiece.mul_zero {i j : ι} (a : GradedPiece F F_lt i) : a * (0 : GradedPiece F F_lt j) = 0 := by
  rw [← QuotientAddGroup.mk_zero, ← QuotientAddGroup.mk_zero]
  induction a using Quotient.ind'
  show Quotient.mk'' _ = Quotient.mk'' _
  rw [Quotient.eq'']
  simp only [ZeroMemClass.coe_zero, mul_zero, QuotientAddGroup.leftRel_apply, add_zero, neg_mem_iff]
  use 0
  simpa only [AddSubgroupClass.coeSubtype, ZeroMemClass.coe_zero, AddSubgroup.coeSubtype]
    using (MulZeroClass.mul_zero _).symm

variable {F} in
theorem GradedPiece.zero_mul {i j : ι} (a : GradedPiece F F_lt i) : (0 : GradedPiece F F_lt j) * a = 0 := by
  rw [← QuotientAddGroup.mk_zero, ← QuotientAddGroup.mk_zero]
  induction a using Quotient.ind'
  change Quotient.mk'' _ = Quotient.mk'' _
  rw [Quotient.eq'']
  simp only [ZeroMemClass.coe_zero, zero_mul, QuotientAddGroup.leftRel_apply, add_zero, neg_mem_iff]
  use 0
  simpa only [AddSubgroupClass.coeSubtype, ZeroMemClass.coe_zero, AddSubgroup.coeSubtype]
    using (MulZeroClass.zero_mul _).symm

lemma GradedPiece.HEq_one_mul {i : ι} (x : GradedPiece F F_lt i) : HEq ((1 : GradedPiece F F_lt 0) * x) x := by
  let rx := Quotient.out' x
  let r1 : (AddSubgroupClass.subtype (F 0)).range := ⟨1, AddMonoidHom.mem_range.mpr (by use 1; rfl)⟩
  apply HEq_eq_mk_eq F F_lt (zero_add i) (one_mul (rx : R))
  convert (gradedMul_def F F_lt r1 rx).symm
  · exact (Quotient.out_eq' x).symm
  · exact (Quotient.out_eq' x).symm
  · rcases rx.2 with ⟨rx', hrx'⟩
    simp [← hrx']

lemma GradedPiece.HEq_mul_one {i : ι} (x : GradedPiece F F_lt i) : HEq (x * (1 : GradedPiece F F_lt 0)) x := by
  let rx := Quotient.out' x
  let r1 : (AddSubgroupClass.subtype (F 0)).range := ⟨1, AddMonoidHom.mem_range.mpr (by use 1; rfl)⟩
  apply HEq_eq_mk_eq F F_lt (add_zero i) (mul_one (rx : R))
  convert (gradedMul_def F F_lt rx r1).symm
  · exact (Quotient.out_eq' x).symm
  · exact (Quotient.out_eq' x).symm
  · rcases rx.2 with ⟨rx', hrx'⟩
    simp [← hrx']

theorem GradedPiece.mul_add {i j : ι} (a : GradedPiece F F_lt i) (b c : GradedPiece F F_lt j) :
    a * (b + c) = a * b + a * c := by
  induction a using Quotient.ind'
  induction b using Quotient.ind'
  induction c using Quotient.ind'
  show Quotient.mk'' _ = Quotient.mk'' _
  rw [Quotient.eq'']
  simp [QuotientAddGroup.leftRel_apply, AddSubgroup.mem_addSubgroupOf]
  rename_i a1 a2 a3
  have : -(a1 * (a2 + a3)).1 + ((a1 * a2).1 + (a1 * a3).1) = 0 := by
    have : -(a1.1 * (a2.1 + a3.1)) + (a1.1 * a2.1 + a1.1 * a3.1) = 0 := by noncomm_ring
    rw [← this]
    rfl
  rw [this]
  exact zero_mem (F_lt (i + j))

theorem GradedPiece.add_mul {i j : ι} (a b : GradedPiece F F_lt i) (c : GradedPiece F F_lt j) :
    (a + b) * c = a * c + b * c := by
  induction a using Quotient.ind'
  induction b using Quotient.ind'
  induction c using Quotient.ind'
  show Quotient.mk'' _ = Quotient.mk'' _
  rw [Quotient.eq'']
  simp [QuotientAddGroup.leftRel_apply, AddSubgroup.mem_addSubgroupOf]
  rename_i a1 a2 a3
  have : -((a1 + a2) * a3).1 + ((a1 * a3).1 + (a2 * a3).1) = 0 := by
    have : -((a1.1 + a2.1) * a3.1) + (a1.1 * a3.1 + a2.1 * a3.1) = 0 := by noncomm_ring
    rw [← this]
    rfl
  rw [this]
  exact zero_mem (F_lt (i + j))

lemma GradedPiece.HEq_mul_assoc {i j k : ι}
    (a : GradedPiece F F_lt i) (b : GradedPiece F F_lt j) (c : GradedPiece F F_lt k) :
    HEq (a * b * c) (a * (b * c)) := by
  let ra := Quotient.out' a
  let rb := Quotient.out' b
  let rc := Quotient.out' c
  apply HEq_eq_mk_eq F F_lt (add_assoc i j k) (mul_assoc (ra : R) rb rc)
  · show a * b * c = ⟦ra * rb * rc⟧
    convert (gradedMul_def F F_lt (ra * rb) rc).symm
    · convert (gradedMul_def F F_lt ra rb).symm
      · exact (Quotient.out_eq' a).symm
      · exact (Quotient.out_eq' b).symm
    · exact (Quotient.out_eq' c).symm
  · show a * (b * c) = ⟦ra * (rb * rc)⟧
    convert (gradedMul_def F F_lt ra (rb * rc)).symm
    · exact (Quotient.out_eq' a).symm
    · convert (gradedMul_def F F_lt rb rc).symm
      · exact (Quotient.out_eq' b).symm
      · exact (Quotient.out_eq' c).symm

end GradedMul

end HasGMul

/-
variable {F} in
lemma Filtration.pow_mem (n : ℕ) {i : ι} (x : F i) : (x : R) ^ n ∈ F (n • i) := by
  induction' n with d hd
  · simpa only [pow_zero, zero_smul] using FilteredRing.one
  simpa only [pow_succ, succ_nsmul] using FilteredRing.mul_mem hd x.2

variable {F} in
def GradedPiece.gnpow (n : ℕ) {i : ι} (x : GradedPiece F i) : GradedPiece F (n • i) :=
  mk ⟨x.out' ^ n, Filtration.pow_mem n x.out⟩

variable {F} in
lemma GradedPiece.gnpow_zero' {i : ι} (x : GradedPiece F i) :
    HEq (gnpow 0 x) (1 : GradedPiece F 0) := by
  let rx : F i := Quotient.out' x
  let r1 : F 0 := ⟨1, FilteredRing.one⟩
  have smul_eq : 0 • i = 0 := by simp only [zero_smul] --?
  apply fooHEq3 F (rx ^ 0) r1 (smul_eq) (pow_zero rx.1) (Filtration.pow_mem 0 rx) r1.2 rfl rfl

@[simp]
lemma foo2 {i j : ι} (x : F i) (y : GradedPiece F j) : mk x * y = mk (x * y.out') := by
  induction y using Quotient.ind'
  rename_i a
  change Quotient.mk'' _ = Quotient.mk'' _
  rw [Quotient.eq'']
  simp only [QuotientAddGroup.leftRel_apply, AddSubgroup.mem_addSubgroupOf]
  have eq : - (x.1 * a) + x * (Quotient.mk' a).out' = x * (- a + (Quotient.mk' a).out') := by
    noncomm_ring
  have ha : -a + (Quotient.mk' a).out' ∈ Filtration.LTSubgroup F j := by
    rw [← QuotientAddGroup.leftRel_apply, ← Quotient.eq'']
    exact Eq.symm (Quotient.out_eq' (Quotient.mk' a))
  convert (Filtration.mul_mem_LTSubgroup' x _ ha )
  exact SetLike.coe_eq_coe.mp eq

variable {F} in
lemma GradedPiece.gnpow_succ' (n : ℕ) {i : ι} (x : GradedPiece F i) :
    HEq (gnpow n.succ x) (gnpow n x * x) := by
  let rx : F i := Quotient.out' x
  have succ_eq : n.succ • i = n • i + i := by simp only [Nat.succ_eq_add_one, succ_nsmul] --?
  apply fooHEq3 F (rx ^ n.succ) (rx ^ n * rx) succ_eq (pow_succ rx.1 n)
    (Filtration.pow_mem n.succ rx) (FilteredRing.mul_mem (Filtration.pow_mem n rx) rx.2) rfl
  apply foo2

variable {F} in
def GradedPiece.natCast (n : ℕ) : GradedPiece F 0 := mk (n • (1 : F 0))

variable {F} in
lemma GradedPiece.natCast_zero : (natCast 0 : GradedPiece F 0) = 0 := by
  show mk (0 • (1 : F 0)) = 0
  simp only [zero_smul, QuotientAddGroup.mk_zero]
  rfl

variable {F} in
lemma GradedPiece.natCast_succ (n : ℕ) :
    (natCast n.succ : GradedPiece F 0) = (natCast n : GradedPiece F 0) + 1 := by
  show mk (n.succ • (1 : F 0)) = mk (n • (1 : F 0)) + 1
  simp only [Nat.succ_eq_add_one, nsmul_eq_mul, Nat.cast_add, Nat.cast_one, mul_one]
  apply Quotient.eq''.mpr
  convert_to Setoid.r (((n : F 0) + 1) * 1) ((n : F 0) * 1 + 1)
  · simp only [mul_one]
  simp only [QuotientAddGroup.leftRel_apply, neg_add_cancel ((n : F 0) + 1)]
  · simp only [mul_one, add_right_inj]; rfl
  simp only [mul_one]
  exact Quotient.eq''.mp rfl

/-# Main Result-/
instance : DirectSum.GSemiring (GradedPiece F) where
  mul_zero := GradedPiece.mul_zero
  zero_mul := GradedPiece.zero_mul
  mul_add := GradedPiece.mul_add
  add_mul := GradedPiece.add_mul
  one_mul := fun ⟨i, a⟩ =>
    Sigma.ext (by simp only [GradedMonoid.fst_mul, GradedMonoid.fst_one, zero_add]) (HEq_one_mul a)
  mul_one := fun ⟨i, a⟩ =>
    Sigma.ext (by simp only [GradedMonoid.fst_mul, GradedMonoid.fst_one, add_zero]) (HEq_mul_one a)
  mul_assoc := fun ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩ => Sigma.ext (add_assoc i j k) (id (HEq_mul_assoc a b c))
  gnpow := GradedPiece.gnpow
  gnpow_zero' := by
    intro ⟨i, a⟩
    apply Sigma.ext
    · show (0 • i) = 0
      simp only [zero_smul]
    exact GradedPiece.gnpow_zero' a
  gnpow_succ' := by
    intro n ⟨i, a⟩
    apply Sigma.ext
    · show n.succ • i = n • i + i
      simp only [Nat.succ_eq_add_one, succ_nsmul]
    simp only [GradedMonoid.snd_mul]
    show HEq (gnpow n.succ a) ((gnpow n a) * a)
    exact gnpow_succ' n a
  natCast := GradedPiece.natCast
  natCast_zero := GradedPiece.natCast_zero
  natCast_succ := GradedPiece.natCast_succ

open DirectSum in
instance : Semiring (⨁ i, GradedPiece F i) := by infer_instance
-/
