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

section GradedRing

#check GradedRing

variable {R : Type u} [Ring R] {σ : Type*} [SetLike σ R] [AddSubgroupClass σ R]

variable (F : ι → σ) (F_lt : outParam <| ι → σ)

section HasGMul

class hasGMul extends IsRingFiltration F F_lt where
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

namespace GradedPiece

variable [hasGMul F F_lt]

def gradedMul {i j : ι} (x : GradedPiece F F_lt i) (y : GradedPiece F F_lt j) : GradedPiece F F_lt (i + j) :=
  Quotient.map₂ (· * ·) (Filtration.mul_equiv_mul F F_lt) x y

instance hMul {i j : ι} :
    HMul (GradedPiece F F_lt i) (GradedPiece F F_lt j) (GradedPiece F F_lt (i + j)) where
  hMul := gradedMul F F_lt

def mk {i : ι} (x : (AddSubgroupClass.subtype (F i)).range) : GradedPiece F F_lt i := ⟦x⟧

omit [OrderedCancelAddCommMonoid ι] in
@[simp]
lemma mk_congr {i : ι} (x y : (AddSubgroupClass.subtype (F i)).range) (h : x = y) : mk F F_lt x = mk F F_lt y := congrArg (mk F F_lt) h

@[simp]
lemma sound {i : ι} (x y : (AddSubgroupClass.subtype (F i)).range) : x ≈ y → mk F F_lt x = mk F F_lt y := Quotient.sound

@[simp]
lemma exact {i : ι} (x y : (AddSubgroupClass.subtype (F i)).range) : mk F F_lt x = mk F F_lt y → x ≈ y := Quotient.exact

omit [OrderedCancelAddCommMonoid ι] [hasGMul F F_lt] in
@[simp]
lemma mk_eq {i : ι} (x : (AddSubgroupClass.subtype (F i)).range) : mk F F_lt x = ⟦x⟧ := rfl



end GradedPiece

end HasGMul

/-
-- implicit variable?
variable {F} in
def GradedPiece.mk {i : ι} (x : F i) : GradedPiece F i := ⟦x⟧

open GradedPiece

instance : OfNat (GradedPiece F i) 0 where
  ofNat := mk (0 : F i)

@[simp]
lemma GradedPiece.mk_inj {i : ι} (x y : F i) (h : x = y) : mk x = mk y := congrArg mk h

@[simp]
lemma GradedPiece.sound {i : ι} (x y : F i) : x ≈ y → mk x = mk y := Quotient.sound

@[simp]
lemma GradedPiece.exact {i : ι} (x y : F i) : mk x = mk y → x ≈ y := Quotient.exact

/-- to be renamed-/
@[simp]
lemma foo1 {i : ι} (x : F i) : mk x = ⟦x⟧ := rfl

/-- to be renamed-/
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

lemma GradedPiece.mk_mul {i j : ι} (x : F i) (y : F j) : mk x * mk y = mk (x * y) := rfl

lemma GradedPiece.mk_zero {i : ι} : mk (0 : F i) = (0 : GradedPiece F i) := rfl

-- If refactor with `GradedPiece.mk`, one should change all `⟦_⟧` to `GradedPiece.mk _`
theorem fooHEq1 {i j : ι} {r : R} (h : i = j) (hi : r ∈ F i) (hj : r ∈ F j) :
    HEq (⟦⟨r, hi⟩⟧ : GradedPiece F i) (⟦⟨r, hj⟩⟧ : GradedPiece F j) :=
  h ▸ HEq.rfl

theorem fooHEq2 {i j : ι} {x : GradedPiece F i} {y : GradedPiece F j} (r : R) (h : i = j)
    (hi : r ∈ F i) (hj : r ∈ F j) (hx : x = ⟦⟨r, hi⟩⟧) (hy : y = ⟦⟨r, hj⟩⟧) : HEq x y :=
  hx ▸ hy ▸ h ▸ HEq.rfl

theorem fooHEq3 {i j : ι} {x : GradedPiece F i} {y : GradedPiece F j} (r s : R)
    (h : i = j) (e : r = s) (hi : r ∈ F i) (hj : s ∈ F j)
    (hx : x = ⟦⟨r, hi⟩⟧) (hy : y = ⟦⟨s, hj⟩⟧) : HEq x y := by
  rw [hx, hy]
  subst e
  exact fooHEq1 F h hi hj

-- Will be easier to use if HMul intances for F i is added and some other refactor is done.
theorem fooHEq4 {i j : ι} {x : GradedPiece F i} {y : GradedPiece F j} (r : F i) (s : F j)
    (h : i = j) (e : (r : R) = s) (hx : x = ⟦r⟧) (hy : y = ⟦s⟧) : HEq x y :=
  fooHEq3 F r s h e r.2 s.2 hx hy


@[local simp]
lemma foo4 {i j : ι} (r : F i) (s : F j) :
  ⟦(⟨r * s, FilteredRing.mul_mem r.2 s.2⟩ : F (i + j))⟧ = gradedMul F ⟦r⟧ ⟦s⟧ := rfl

/-- Delete-/
-- This is an example of using `fooHEq4` lemma (without refactor)
lemma foo_bar {i : ι} (x : GradedPiece F i) : HEq (gradedMul F (0 : GradedPiece F 0) x) (0 : GradedPiece F i) := by
  let rx : F i := Quotient.out' x
  let r00 : F 0 := ⟨0, zero_mem _⟩
  let r0i : F i := ⟨0, zero_mem _⟩
  apply fooHEq3 F (r00 * rx) r0i (zero_add i) (zero_mul (rx : R))
  convert (foo4 F r00 rx).symm
  exact (Quotient.out_eq' x).symm
  rfl
-/
/-
instance : GradedMonoid.GMul (GradedPiece F) where
  mul := gradedMul F

instance : GradedMonoid.GOne (GradedPiece F) where
  one := .mk ⟨1, FilteredRing.one⟩

variable {F} in
theorem GradedPiece.mul_zero {i j : ι} (a : GradedPiece F i) : a * (0 : GradedPiece F j) = 0 := by
  rw [← QuotientAddGroup.mk_zero, ← QuotientAddGroup.mk_zero]
  induction a using Quotient.ind'
  change Quotient.mk'' _ = Quotient.mk'' _
  rw [Quotient.eq'']
  simp only [ZeroMemClass.coe_zero, mul_zero,
    QuotientAddGroup.leftRel_apply, add_zero, neg_mem_iff]
  refine Filtration.mul_mem_LTSubgroup' _ 0 ?h.hy
  exact zero_mem _

variable {F} in
theorem GradedPiece.zero_mul {i j : ι} (a : GradedPiece F i) : (0 : GradedPiece F j) * a = 0 := by
  rw [← QuotientAddGroup.mk_zero, ← QuotientAddGroup.mk_zero]
  induction a using Quotient.ind'
  change Quotient.mk'' _ = Quotient.mk'' _
  rw [Quotient.eq'']
  simp only [ZeroMemClass.coe_zero, zero_mul,
    QuotientAddGroup.leftRel_apply, add_zero, neg_mem_iff]
  refine Filtration.mul_mem_LTSubgroup 0 _ ?h.hy
  exact zero_mem _

variable {F} in
theorem GradedPiece.mul_add {i j : ι} (a : GradedPiece F i) (b c : GradedPiece F j) :
    a * (b + c) = a * b + a * c := by
  induction a using Quotient.ind'
  induction b using Quotient.ind'
  induction c using Quotient.ind'
  change Quotient.mk'' _ = Quotient.mk'' _
  rw [Quotient.eq'']
  simp [QuotientAddGroup.leftRel_apply, AddSubgroup.mem_addSubgroupOf]
  rename_i a1 a2 a3
  have : -(a1 * (a2 + a3)) + (a1 * a2 + a1 * a3) = 0 := by
    have : -(a1.1 * (a2 + a3)) + (a1 * a2 + a1 * a3) = 0 := by
      noncomm_ring
    exact ZeroMemClass.coe_eq_zero.mp this
  rw [this]
  exact zero_mem _

variable {F} in
theorem GradedPiece.add_mul {i j : ι} (a b : GradedPiece F i) (c : GradedPiece F j) :
    (a + b) * c = a * c + b * c := by
  induction a using Quotient.ind'
  induction b using Quotient.ind'
  induction c using Quotient.ind'
  change Quotient.mk'' _ = Quotient.mk'' _
  rw [Quotient.eq'']
  simp [QuotientAddGroup.leftRel_apply, AddSubgroup.mem_addSubgroupOf]
  rename_i a1 a2 a3
  have : -((a1 + a2) * a3) + (a1 * a3 + a2 * a3) = 0 := by
    have : -((a1.1 + a2) * a3) + (a1 * a3 + a2 * a3) = 0 := by
      noncomm_ring
    exact ZeroMemClass.coe_eq_zero.mp this
  rw [this]
  exact zero_mem _


variable {F} in
lemma GradedPiece.HEq_one_mul {i : ι} (x : GradedPiece F i) : HEq ((1 : GradedPiece F 0) * x) x := by
  let rx : F i := Quotient.out' x
  let r1 : F 0 := ⟨1, FilteredRing.one⟩
  apply fooHEq3 F (r1 * rx) rx (zero_add i) (one_mul (rx : R))
  convert (foo4 F r1 rx).symm
  all_goals exact (Quotient.out_eq' x).symm

variable {F} in
lemma GradedPiece.HEq_mul_one {i : ι} (x : GradedPiece F i) : HEq (x * (1 : GradedPiece F 0)) x := by
  let rx : F i := Quotient.out' x
  let r1 : F 0 := ⟨1, FilteredRing.one⟩
  apply fooHEq3 F (rx * r1) rx (add_zero i) (mul_one (rx : R))
  convert (foo4 F rx r1).symm
  all_goals exact (Quotient.out_eq' x).symm

variable {F} in
lemma GradedPiece.HEq_mul_assoc {i j k : ι}
    (a : GradedPiece F i) (b : GradedPiece F j) (c : GradedPiece F k) :
    HEq (a * b * c) (a * (b * c)) := by
  let ra : F i := Quotient.out' a
  let rb : F j := Quotient.out' b
  let rc : F k := Quotient.out' c
  apply fooHEq3 F (ra * rb * rc) (ra * (rb * rc)) (add_assoc i j k) (mul_assoc (ra : R) rb rc)
  · show a * b * c = ⟦ra * rb * rc⟧
    convert (foo4 F (ra * rb) rc).symm
    · convert (foo4 F ra rb).symm
      · exact (Quotient.out_eq' a).symm
      · exact (Quotient.out_eq' b).symm
    · exact (Quotient.out_eq' c).symm
  · show a * (b * c) = ⟦ra * (rb * rc)⟧
    convert (foo4 F ra (rb * rc)).symm
    · exact (Quotient.out_eq' a).symm
    · convert (foo4 F rb rc).symm
      · exact (Quotient.out_eq' b).symm
      · exact (Quotient.out_eq' c).symm

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
