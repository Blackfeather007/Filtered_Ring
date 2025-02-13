/-
Copyright (c) 2024 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Wanyi He, Jiedong Jiang
-/
import FilteredRing.Basic
import FilteredRing.MissingCoersion
/-!

-/

section GeneralGraded

variable {ι : Type*}

variable {A : Type*} [AddCommGroup A] {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]

variable (F : ι → σ) (F_lt : outParam <| ι → σ)

@[nolint unusedArguments]
instance [Preorder ι] [IsFiltration F F_lt] (i : ι) :
    Setoid (F i) :=
  QuotientAddGroup.leftRel (((F_lt i) : AddSubgroup A).addSubgroupOf ((F i) : AddSubgroup A))

/-- `GradedPiece i` of the associated graded ring is defined as `F i` quotient by `F_lt i`-/
abbrev GradedPiece (i : ι) := ((F i) : AddSubgroup A) ⧸ ((F_lt i) : AddSubgroup A).addSubgroupOf ((F i) : AddSubgroup A)

namespace GradedPiece

/--Obtaining an element of `GradedPiece i` from an element of `F i`-/
def mk {i : ι} (x : F i) : GradedPiece F F_lt i := ⟦x⟧

section

@[simp]
lemma mk_eq {i : ι} (x : F i) : mk F F_lt x = ⟦x⟧ := rfl

lemma mk_zero {i : ι} : mk F F_lt 0  = (0 : GradedPiece F F_lt i) := rfl

lemma HEq_rfl {i j : ι} {r : A} (h : i = j)
    (hi : r ∈ F i) (hj : r ∈F j) :
    HEq (mk F F_lt ⟨r, hi⟩) (mk F F_lt ⟨r, hj⟩) :=
  h ▸ HEq.rfl

lemma HEq_eq_mk_eq {i j : ι} {x : GradedPiece F F_lt i} {y : GradedPiece F F_lt j} {r s : A}
    (h : i = j) (e : r = s) (hi : r ∈ F i) (hj : s ∈ F j)
    (hx : x = mk F F_lt ⟨r, hi⟩) (hy : y = mk F F_lt ⟨s, hj⟩) : HEq x y := by
  rw [hx, hy]
  subst e
  exact HEq_rfl F F_lt h hi hj

-- Will be easier to use if HMul intances for F i is added and some other refactor is done.
lemma HEq_eq_mk_coe_eq {i j : ι} {x : GradedPiece F F_lt i} {y : GradedPiece F F_lt j}
    (r : F i) (s : F j) (h : i = j) (e : (r : A) = (s : A))
    (hx : x = mk F F_lt r) (hy : y = mk F F_lt s) : HEq x y :=
  HEq_eq_mk_eq F F_lt h e r.2 (e ▸ s.2) hx hy

end

lemma mk_congr {i : ι} (x y : F i) (h : x = y) :
    mk F F_lt x = mk F F_lt y := congrArg (mk F F_lt) h

lemma sound [Preorder ι] [IsFiltration F F_lt] {i : ι}
    (x y : F i) : x ≈ y → mk F F_lt x = mk F F_lt y :=
  Quotient.sound

@[simp]
lemma exact [Preorder ι] [IsFiltration F F_lt] {i : ι}
    (x y : F i) : mk F F_lt x = mk F F_lt y → x ≈ y :=
  Quotient.exact

end GradedPiece

end GeneralGraded

section GradedRing

variable {ι : Type*}

variable {R : Type*} [Ring R] {σ : Type*} [SetLike σ R]

instance [OrderedAddCommMonoid ι] [AddSubgroupClass σ R] (F : ι → σ) (F_lt : outParam <| ι → σ) [IsRingFiltration F F_lt] :
    One (GradedPiece F F_lt 0) where
  one := ⟦⟨1, IsRingFiltration.one_mem⟩⟧

variable (F : ι → σ) (F_lt : outParam <| ι → σ)

section HasGMul

/--The class of filtrations that can obtain a well defined `GradedMul`
from the multiplication `F i → F j → F (i + j)` -/
class hasGMul [OrderedAddCommMonoid ι] extends IsRingFiltration F F_lt : Prop where
  F_lt_mul_mem {i j : ι} {x y} : x ∈ F_lt i → y ∈ F j → x * y ∈ F_lt (i + j)
  mul_F_lt_mem {i j : ι} {x y} : x ∈ F i → y ∈ F_lt j → x * y ∈ F_lt (i + j)

lemma hasGMul_int (F : ℤ → σ) (mono : ∀ {a b : ℤ}, a ≤ b → F a ≤ F b) (one_mem : 1 ∈ F 0)
    (mul_mem : ∀ {i j x y}, x ∈ F i → y ∈ F j → x * y ∈ F (i + j)) :
    hasGMul F (fun n ↦ F (n - 1)) := {
    IsRingFiltration_int F mono one_mem mul_mem with
    F_lt_mul_mem := fun h1 h2 ↦ by
      have := mul_mem h1 h2
      rwa [sub_add_eq_add_sub] at this
    mul_F_lt_mem := fun h1 h2 ↦ by
      have := mul_mem h1 h2
      rwa [add_sub_assoc'] at this }

lemma hasGMul_AddSubgroup (F : ι → AddSubgroup R) (F_lt : outParam <| ι → AddSubgroup R)
    [OrderedCancelAddCommMonoid ι] [IsRingFiltration F F_lt] : hasGMul F F_lt where
  F_lt_mul_mem := by
    intro i j x y hx hy
    let S : AddSubgroup R := {
      carrier := {z | z * y ∈ F_lt (i + j)}
      add_mem' := fun ha hb ↦ by simp only [Set.mem_setOf_eq, add_mul, add_mem ha.out hb.out]
      zero_mem' := by simp only [Set.mem_setOf_eq, zero_mul, zero_mem]
      neg_mem' := by simp only [Set.mem_setOf_eq, neg_mul, neg_mem_iff, imp_self, implies_true]}
    exact IsFiltration.is_sup S i (fun k hk z hz ↦
      IsFiltration.is_le (add_lt_add_right hk j) (IsRingFiltration.mul_mem hz hy)) hx
  mul_F_lt_mem := by
    intro i j x y hx hy
    let S : AddSubgroup R := {
      carrier := {z | x * z ∈ F_lt (i + j)}
      add_mem' := fun ha hb ↦ by simp only [Set.mem_setOf_eq, mul_add, add_mem ha.out hb.out]
      zero_mem' := by simp only [Set.mem_setOf_eq, mul_zero, zero_mem]
      neg_mem' := by simp only [Set.mem_setOf_eq, mul_neg, neg_mem_iff, imp_self, implies_true]}
    exact IsFiltration.is_sup S j (fun k hk z hz ↦
      IsFiltration.is_le (add_lt_add_left hk i) (IsRingFiltration.mul_mem hx hz)) hy

variable [OrderedAddCommMonoid ι] [AddSubgroupClass σ R]

/--The multiplication `F i → F j → F (i + j)` defined as the multiplication of its value. -/
def IsRingFiltration.hMul [IsRingFiltration F F_lt] (i j : ι)
    (x : F i) (y : F j) : F (i + j) where
  val := x * y
  property := by
    simp [IsRingFiltration.mul_mem x.2 y.2]

instance [IsRingFiltration F F_lt] {i j : ι} :
    HMul (F i) (F j) (F (i + j)) where
  hMul := IsRingFiltration.hMul F F_lt i j

lemma hasGMul.mul_equiv_mul [hasGMul F F_lt] {i j : ι}
    ⦃x₁ x₂ : F i⦄ (hx : x₁ ≈ x₂)
    ⦃y₁ y₂ : F j⦄ (hy : y₁ ≈ y₂) : x₁ * y₁ ≈ x₂ * y₂ := by
  simp only [HasEquiv.Equiv, QuotientAddGroup.leftRel_apply, AddSubgroup.mem_addSubgroupOf,
    AddSubgroup.coe_add, NegMemClass.coe_neg, AddMonoidHom.mem_range, AddSubgroupClass.coeSubtype,
    Subtype.exists, exists_prop, exists_eq_right] at hx hy ⊢
  have eq : - (x₁ * y₁ : R) + (x₂ * y₂ : R) = (- x₁ + x₂ : R) * y₁ + x₂ * (- y₁ + y₂ : R) := by
    noncomm_ring
  have eq : - (x₁ * y₁) + (x₂ * y₂) = (- x₁ + x₂) * y₁ + x₂ * (- y₁ + y₂) := SetLike.coe_eq_coe.mp eq
  rw [eq]
  exact add_mem (hasGMul.F_lt_mul_mem (F := F) hx y₁.2) (hasGMul.mul_F_lt_mem (F := F) x₂.2 hy)

/--The multiplication `GradedPiece F F_lt i → GradedPiece F F_lt j → GradedPiece F F_lt (i + j)`
lifted from the multiplication `F i → F j → F (i + j)`-/
def hasGMul.gradedMul [hasGMul F F_lt] {i j : ι} (x : GradedPiece F F_lt i)
    (y : GradedPiece F F_lt j) : GradedPiece F F_lt (i + j) :=
  Quotient.map₂ (· * ·) (hasGMul.mul_equiv_mul F F_lt) x y

instance hMul [hasGMul F F_lt] {i j : ι} :
    HMul (GradedPiece F F_lt i) (GradedPiece F F_lt j) (GradedPiece F F_lt (i + j)) where
  hMul := hasGMul.gradedMul F F_lt

namespace GradedPiece

section HEq

lemma mk_mul [hasGMul F F_lt] {i j : ι}
    (x : F i) (y : F j) :
    mk F F_lt x * mk F F_lt y = mk F F_lt (x * y) := rfl

lemma gradedMul_def [hasGMul F F_lt] {i j : ι}
    (x : F i) (y : F j) :
    mk F F_lt (IsRingFiltration.hMul F F_lt i j x y) =
    hasGMul.gradedMul F F_lt (mk F F_lt x) (mk F F_lt y) := rfl

end HEq

end GradedPiece

namespace GradedMul

open GradedPiece

instance [hasGMul F F_lt] : GradedMonoid.GMul (GradedPiece F F_lt) where
  mul := hasGMul.gradedMul F F_lt

instance [IsRingFiltration F F_lt] : GradedMonoid.GOne (GradedPiece F F_lt) where
  one := (1 : GradedPiece F F_lt 0)

lemma GradedPiece.HEq_one_mul [hasGMul F F_lt] {i : ι} (x : GradedPiece F F_lt i) :
    HEq ((1 : GradedPiece F F_lt 0) * x) x := by
  let rx := Quotient.out x
  let r1 : (F 0) := ⟨1, IsRingFiltration.one_mem⟩
  apply HEq_eq_mk_eq F F_lt (zero_add i) (one_mul (rx : R))
  · convert (gradedMul_def F F_lt r1 rx).symm
    exact (Quotient.out_eq' x).symm
  · exact (Quotient.out_eq' x).symm
  · simp

lemma GradedPiece.HEq_mul_one [hasGMul F F_lt] {i : ι} (x : GradedPiece F F_lt i) :
    HEq (x * (1 : GradedPiece F F_lt 0)) x := by
  let rx := Quotient.out x
  let r1 : (F 0) := ⟨1, IsRingFiltration.one_mem⟩
  apply HEq_eq_mk_eq F F_lt (add_zero i) (mul_one (rx : R))
  · convert (gradedMul_def F F_lt rx r1).symm
    exact (Quotient.out_eq' x).symm
  · exact (Quotient.out_eq' x).symm
  · simp

lemma GradedPiece.HEq_mul_assoc [hasGMul F F_lt] {i j k : ι}
    (a : GradedPiece F F_lt i) (b : GradedPiece F F_lt j) (c : GradedPiece F F_lt k) :
    HEq (a * b * c) (a * (b * c)) := by
  let ra := Quotient.out a
  let rb := Quotient.out b
  let rc := Quotient.out c
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

omit [AddSubgroupClass σ R] in
lemma Filtration.pow_mem [IsRingFiltration F F_lt] (n : ℕ) {i : ι}
    (x : F i) : (x : R) ^ n ∈ (F (n • i)) := by
  induction' n with d hd
  · simpa using IsRingFiltration.one_mem
  · rw [pow_succ]
    simpa [succ_nsmul i d] using (IsRingFiltration.mul_mem hd x.2)

lemma Filtration.pow_lift [hasGMul F F_lt] (n : ℕ) {i : ι}
    (x₁ x₂ : F i) (h : x₁ ≈ x₂) :
    (⟨x₁ ^ n, Filtration.pow_mem F F_lt n x₁⟩ : (F (n • i))) ≈
    (⟨x₂ ^ n, Filtration.pow_mem F F_lt n x₂⟩ : (F (n • i))) := by
  induction' n with d hd
  · simp only [pow_zero, mk_eq, exact]
  · simp only [pow_succ]
    simp only [HasEquiv.Equiv, QuotientAddGroup.leftRel_apply, AddSubgroup.mem_addSubgroupOf,
      AddSubgroup.coe_add, NegMemClass.coe_neg, AddMonoidHom.mem_range, AddSubgroupClass.coeSubtype,
      Subtype.exists, exists_prop, exists_eq_right] at h hd ⊢
    have mem1 : x₁.1 ^ d * x₂.1 - x₁.1 ^ d * x₁.1 ∈ F_lt ((d + 1) • i) := by
      rw [← mul_sub, sub_eq_neg_add]
      have := Filtration.pow_mem F F_lt d x₁
      simp only [AddMonoidHom.mem_range, AddSubgroupClass.coeSubtype, Subtype.exists, exists_prop,
        exists_eq_right] at this
      simpa [succ_nsmul i d] using hasGMul.mul_F_lt_mem this h
    have mem2 : x₂.1 ^ d * x₂.1 - x₁.1 ^ d * x₂.1 ∈ F_lt ((d + 1) • i) := by
      rw [← sub_mul, sub_eq_neg_add]
      simp [succ_nsmul i d]
      exact hasGMul.F_lt_mul_mem hd x₂.2
    show -(x₁.1 ^ d * x₁.1) + x₂.1 ^ d * x₂.1 ∈ (F_lt ((d + 1) • i))
    have : -(x₁.1 ^ d * x₁.1) + x₂.1 ^ d * x₂.1 =
      x₁.1 ^ d * x₂.1 - x₁.1 ^ d * x₁.1 + (x₂.1 ^ d * x₂.1 - x₁.1 ^ d * x₂.1) := by abel
    rw [this]
    exact add_mem mem1 mem2

/--The graded nat power between graded pieces. -/
def GradedPiece.gnpow [hasGMul F F_lt] (n : ℕ) {i : ι} :
    GradedPiece F F_lt i → GradedPiece F F_lt (n • i) :=
  Quotient.map (fun x ↦ ⟨x.1 ^ n, Filtration.pow_mem F F_lt n x⟩)
  (fun x₁ x₂ h ↦ Filtration.pow_lift F F_lt n x₁ x₂ h)

lemma gnpow_def [hasGMul F F_lt] (n : ℕ) {i : ι} (x : F i) :
    mk F F_lt ⟨x.1 ^ n, Filtration.pow_mem F F_lt n x⟩ = GradedPiece.gnpow F F_lt n (mk F F_lt x) :=
  rfl

lemma GradedPiece.gnpow_zero' [hasGMul F F_lt] {i : ι} (x : GradedPiece F F_lt i) :
    HEq (gnpow F F_lt 0 x) (1 : GradedPiece F F_lt 0) := by
  let rx := Quotient.out x
  let r1 : (F 0) := ⟨1, IsRingFiltration.one_mem⟩
  apply HEq_eq_mk_eq F F_lt (zero_nsmul i) (pow_zero rx.1) (Filtration.pow_mem F F_lt 0 rx)
    r1.2 _ rfl
  simp only [gnpow_def F F_lt 0 rx, rx, mk_eq]
  nth_rw 1 [← Quotient.out_eq x]

lemma GradedPiece.gnpow_succ' [hasGMul F F_lt] (n : ℕ) {i : ι} (x : GradedPiece F F_lt i) :
    HEq (gnpow F F_lt n.succ x) (gnpow F F_lt n x * x) := by
  let rx := Quotient.out x
  have mk_rx : mk F F_lt rx = x := by
    nth_rw 1 [← Quotient.out_eq x]
    rfl
  have : rx.1 ^ n * rx.1 ∈ (F (n • i + i)) := IsRingFiltration.mul_mem (Filtration.pow_mem F F_lt n rx) rx.2
  apply HEq_eq_mk_eq F F_lt (succ_nsmul i n) (pow_succ rx.1 n) (Filtration.pow_mem F F_lt (n + 1) rx) this
  · rw [gnpow_def, mk_rx]
  · rw [← mk_rx, ← gnpow_def]
    rfl

instance [hasGMul F F_lt] : GradedMonoid.GMonoid (GradedPiece F F_lt) where
  one_mul := fun ⟨i, a⟩ => Sigma.ext (by simp) (GradedPiece.HEq_one_mul F F_lt a)
  mul_one := fun ⟨i, a⟩ => Sigma.ext (by simp) (GradedPiece.HEq_mul_one F F_lt a)
  mul_assoc := fun ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩ =>
    Sigma.ext (add_assoc i j k) (GradedPiece.HEq_mul_assoc F F_lt a b c)
  gnpow := GradedPiece.gnpow F F_lt
  gnpow_zero' := fun ⟨i, a⟩ ↦ Sigma.ext (zero_nsmul i) (GradedPiece.gnpow_zero' F F_lt a)
  gnpow_succ' :=  fun n ⟨i, a⟩ ↦ Sigma.ext (succ_nsmul i n) (GradedPiece.gnpow_succ' F F_lt n a)

lemma GradedPiece.mul_zero [hasGMul F F_lt] {i j : ι} (a : GradedPiece F F_lt i) :
    a * (0 : GradedPiece F F_lt j) = 0 := by
  rw [← QuotientAddGroup.mk_zero, ← QuotientAddGroup.mk_zero]
  induction a using Quotient.ind'
  show Quotient.mk'' _ = Quotient.mk'' _
  rw [Quotient.eq'']
  simp only [ZeroMemClass.coe_zero, mul_zero, QuotientAddGroup.leftRel_apply, add_zero, neg_mem_iff]
  show _ * (0 : R) ∈ (F_lt (i + j))
  simpa only [MulZeroClass.mul_zero] using zero_mem (F_lt (i + j))


lemma GradedPiece.zero_mul [hasGMul F F_lt] {i j : ι} (a : GradedPiece F F_lt i) :
    (0 : GradedPiece F F_lt j) * a = 0 := by
  rw [← QuotientAddGroup.mk_zero, ← QuotientAddGroup.mk_zero]
  induction a using Quotient.ind'
  change Quotient.mk'' _ = Quotient.mk'' _
  rw [Quotient.eq'']
  simp only [ZeroMemClass.coe_zero, zero_mul, QuotientAddGroup.leftRel_apply, add_zero, neg_mem_iff]
  show (0 : R) * _ ∈ (F_lt (j + i))
  simpa only [MulZeroClass.zero_mul] using zero_mem (F_lt (j + i))

lemma GradedPiece.mul_add [hasGMul F F_lt] {i j : ι} (a : GradedPiece F F_lt i)
    (b c : GradedPiece F F_lt j) : a * (b + c) = a * b + a * c := by
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

lemma GradedPiece.add_mul [hasGMul F F_lt] {i j : ι} (a b : GradedPiece F F_lt i)
    (c : GradedPiece F F_lt j) : (a + b) * c = a * c + b * c := by
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

/--The nat scalar multiple in `GradedPiece F F_lt 0`-/
def GradedPiece.natCast [IsRingFiltration F F_lt] (n : ℕ) : GradedPiece F F_lt 0 :=
  mk F F_lt (n • ⟨1, IsRingFiltration.one_mem⟩)

lemma GradedPiece.natCast_zero [IsRingFiltration F F_lt] :
    (natCast F F_lt 0 : GradedPiece F F_lt 0) = 0 := by
  show mk F F_lt (0 • ⟨1, IsRingFiltration.one_mem⟩) = 0
  simp only [zero_smul, mk_eq]
  rfl

lemma GradedPiece.natCast_succ [IsRingFiltration F F_lt] (n : ℕ) :
    (natCast F F_lt n.succ : GradedPiece F F_lt 0) =
    (natCast F F_lt n : GradedPiece F F_lt 0) + 1 := by
  show mk F F_lt (n.succ • ⟨1, IsRingFiltration.one_mem⟩) =
    mk F F_lt ((n • ⟨1, IsRingFiltration.one_mem⟩) + (⟨1, IsRingFiltration.one_mem⟩))
  simp [add_one_mul]

instance [hasGMul F F_lt] : DirectSum.GSemiring (GradedPiece F F_lt) :=
{ GradedMul.instGMonoidGradedPieceOfHasGMul F F_lt with
  mul_zero := GradedPiece.mul_zero F F_lt
  zero_mul := GradedPiece.zero_mul F F_lt
  mul_add := GradedPiece.mul_add F F_lt
  add_mul := GradedPiece.add_mul F F_lt
  natCast := GradedPiece.natCast F F_lt
  natCast_zero := GradedPiece.natCast_zero F F_lt
  natCast_succ := GradedPiece.natCast_succ F F_lt }

/--The int scalar multiple in `GradedPiece F F_lt 0`-/
def GradedPiece.intCast [IsRingFiltration F F_lt] (n : ℤ) : GradedPiece F F_lt 0 :=
  mk F F_lt (n • ⟨1, IsRingFiltration.one_mem⟩)

lemma GradedPiece.intCast_ofNat [IsRingFiltration F F_lt] (n : ℕ) :
    intCast F F_lt n = natCast F F_lt n := by
  show mk F F_lt ((n : ℤ) • ⟨1, IsRingFiltration.one_mem⟩) =
    mk F F_lt (n • ⟨1, IsRingFiltration.one_mem⟩)
  simp

lemma GradedPiece.intCast_negSucc_ofNat [IsRingFiltration F F_lt] (n : ℕ) :
    intCast F F_lt (Int.negSucc n) = - (natCast F F_lt (n + 1)) := by
  show mk F F_lt ((Int.negSucc n) • ⟨1, IsRingFiltration.one_mem⟩) =
    - mk F F_lt ((n + 1) • ⟨1, IsRingFiltration.one_mem⟩)
  simp only [negSucc_zsmul, nsmul_eq_mul, Nat.cast_add, Nat.cast_one, mk_eq]
  rfl

instance [hasGMul F F_lt] : DirectSum.GRing (GradedPiece F F_lt) where
  intCast := GradedPiece.intCast F F_lt
  intCast_ofNat := GradedPiece.intCast_ofNat F F_lt
  intCast_negSucc_ofNat := GradedPiece.intCast_negSucc_ofNat F F_lt

open DirectSum in
instance [hasGMul F F_lt] [DecidableEq ι] : Ring (⨁ i, GradedPiece F F_lt i) :=
  DirectSum.ring (GradedPiece F F_lt)

end GradedMul

section GradedAlgebra

open GradedPiece

variable {R : Type*} [CommRing R] {A : Type*} [Ring A] [Algebra R A]

variable {ι : Type*} [OrderedAddCommMonoid ι]

variable (F : ι → Submodule R A) (F_lt : outParam <| ι → Submodule R A)

instance (i : ι) : Module R (GradedPiece F F_lt i) :=
  inferInstanceAs (Module R ((F i)⧸(Submodule.comap (F i).subtype (F_lt i))))

def GradedPiece.algebraMap [IsRingFiltration F F_lt] : R →+ GradedPiece F F_lt 0 where
  toFun r := (mk F F_lt (r • (⟨1, IsRingFiltration.one_mem⟩ : F 0)))
  map_zero' := by
    simp
    rfl
  map_add' x y := by
    simp [add_smul]
    rfl

lemma GradedPiece.algebraMap.map_mul [hasGMul F F_lt] : GradedMonoid.mk 0
    ((GradedPiece.algebraMap F F_lt) (r * s)) = GradedMonoid.mk (0 + 0) (GradedMonoid.GMul.mul
    ((GradedPiece.algebraMap F F_lt) r) ((GradedPiece.algebraMap F F_lt) s)) := by
  congr
  · rw [zero_add]
  · show HEq (mk F F_lt ((r * s) • 1)) _
    rw [mul_comm r s]
    have : ((s * r) • (1 : F 0)).1 = (r • (1 : F 0)).1 * (s • (1 : F 0)).1 := by
      simp only [SetLike.val_smul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
      show (s * r) • (1 : A) = s • r • ((1 : A) * (1 : A))
      simpa using mul_smul s r (1 : A)
    apply HEq_eq_mk_eq F F_lt (AddZeroClass.zero_add 0).symm this ((s * r) • (1 : F 0)).2
      (IsRingFiltration.mul_mem (r • (1 : F 0)).2 (s • (1 : F 0)).2) rfl rfl

lemma GradedPiece.algebraMap.commutes [hasGMul F F_lt] (r : R) (i : ι) (a : GradedPiece F F_lt i) :
    HEq ((mk F F_lt (r • (⟨1, IsRingFiltration.one_mem⟩ : F 0))) * a)
    (a * (mk F F_lt (r • (⟨1, IsRingFiltration.one_mem⟩ : F 0)))) := by
  have : mk F F_lt a.out = a := by simp only [mk_eq, Quotient.out_eq]
  have eq1 : (mk F F_lt (r • (⟨1, IsRingFiltration.one_mem⟩ : F 0))) * a =
    (mk F F_lt ((r • (⟨1, IsRingFiltration.one_mem⟩ : F 0)) * a.out)) := by
    nth_rw 1 [← this]
    rfl
  have eq2 : a * (mk F F_lt (r • (⟨1, IsRingFiltration.one_mem⟩ : F 0))) =
    (mk F F_lt (a.out * (r • (⟨1, IsRingFiltration.one_mem⟩ : F 0)))) := by
    nth_rw 1 [← this]
    rfl
  refine HEq_eq_mk_coe_eq F F_lt _ _ (add_comm 0 i) ?e eq1 eq2
  show (r • (1 : A)) * a.out.val = a.out.val * (r • (1 : A))
  simp

lemma GradedPiece.algebraMap.smul_def [hasGMul F F_lt] (r : R) (i : ι) (a : GradedPiece F F_lt i) :
    HEq (r • a) ((mk F F_lt (r • (⟨1, IsRingFiltration.one_mem⟩ : F 0))) * a) := by
  have : mk F F_lt a.out = a := by simp only [mk_eq, Quotient.out_eq]
  have eq1 : r • a = (mk F F_lt (r • (⟨a.out.1, a.out.2⟩ : F i))) := by
    nth_rw 1 [← this]
    rfl
  have eq2 : (mk F F_lt (r • (⟨1, IsRingFiltration.one_mem⟩ : F 0))) * a =
    (mk F F_lt ((r • (⟨1, IsRingFiltration.one_mem⟩ : F 0)) * a.out)) := by
    nth_rw 1 [← this]
    rfl
  refine HEq_eq_mk_coe_eq F F_lt _ _ (zero_add i).symm ?e eq1 eq2
  show r • a.out.val = (r • (1 : A)) * a.out.val
  simp

instance [hasGMul F F_lt] : DirectSum.GAlgebra R (GradedPiece F F_lt) where
  toFun := GradedPiece.algebraMap F F_lt
  map_one := by
    simp only [GradedPiece.algebraMap, GradedPiece.mk_eq, AddMonoidHom.coe_mk, ZeroHom.coe_mk, one_smul]
    rfl
  map_mul r s := GradedPiece.algebraMap.map_mul F F_lt
  commutes r := fun ⟨i, a⟩ ↦ Sigma.ext (by simp [add_comm]) (GradedPiece.algebraMap.commutes F F_lt r i a)
  smul_def r := fun ⟨i, a⟩ ↦ Sigma.ext (by
    --missing simp lemma
    have : (GradedMonoid.mk 0 ((GradedPiece.algebraMap F F_lt) r)).fst = 0 := rfl
    simp [this]) (GradedPiece.algebraMap.smul_def F F_lt r i a)

end GradedAlgebra

end HasGMul

end GradedRing

section GradedModule

variable {ι : Type*} [OrderedCancelAddCommMonoid ι]

variable {R : Type*} [Ring R] {σ : Type*} [SetLike σ R]

variable (F : ι → σ) (F_lt : outParam <| ι → σ)

variable {M : Type*} {ιM : Type*} [OrderedCancelAddCommMonoid ιM] [AddAction ι ιM]
  {σM : Type*} [SetLike σM M]

section hasGSMul

/--The class of filtrations that can obtain a well defined `GradedSMul`
from the multiplication `F i → FM j → FM (i +ᵥ j)` -/
class hasGSMul [AddCommMonoid M] [Module R M] [isfil : IsRingFiltration F F_lt] (FM : ιM → σM)
    (FM_lt : outParam <| ιM → σM) extends IsModuleFiltration F F_lt FM FM_lt : Prop where
  F_lt_smul_mem {i : ι} {j : ιM} {x y} : x ∈ F_lt i → y ∈ FM j → x • y ∈ FM_lt (i +ᵥ j)
  smul_F_lt_mem {i : ι} {j : ιM} {x y} : x ∈ F i → y ∈ FM_lt j → x • y ∈ FM_lt (i +ᵥ j)

lemma hasGSMul_int [AddCommMonoid M] [Module R M] (F : ℤ → σ)
    (mono : ∀ {a b : ℤ}, a ≤ b → F a ≤ F b) (one_mem : 1 ∈ F 0)
    (mul_mem : ∀ {i j x y}, x ∈ F i → y ∈ F j → x * y ∈ F (i + j)) (F' : ℤ → σM)
    (mono' : ∀ {a b : ℤ}, a ≤ b → F' a ≤ F' b)
    (smul_mem : ∀ {i j x y}, x ∈ F i → y ∈ F' j → x • y ∈ F' (i + j)) :
    hasGSMul (isfil := IsRingFiltration_int F mono one_mem mul_mem)
    F (fun n ↦ F (n - 1)) F' (fun n ↦ F' (n - 1)) :=
  letI := IsRingFiltration_int F mono one_mem mul_mem
  letI := IsModuleFiltration_int F mono one_mem mul_mem F' mono' smul_mem
{ F_lt_smul_mem := fun {i j x y} hx hy ↦ by
    simpa [add_sub_right_comm i j 1] using IsModuleFiltration.smul_mem hx hy
  smul_F_lt_mem := fun {i j x y} hx hy ↦ by
    simpa [add_sub_assoc i j 1] using IsModuleFiltration.smul_mem hx hy}

variable [AddSubgroupClass σ R] [AddCommGroup M] [Module R M] [AddSubgroupClass σM M]

lemma hasGSMul_AddSubgroup [IsOrderedCancelVAdd ι ιM]
    (F : ι → AddSubgroup R) (F_lt : outParam <| ι → AddSubgroup R)
    [IsRingFiltration F F_lt] (FM : ιM → AddSubgroup M) (FM_lt : outParam <| ιM → AddSubgroup M)
    [IsModuleFiltration F F_lt FM FM_lt] : hasGSMul F F_lt FM FM_lt where
  F_lt_smul_mem := by
    intro i j x y hx hy
    let S : AddSubgroup R := {
      carrier := {z : R | z • y ∈ FM_lt (i +ᵥ j)}
      add_mem' := fun ha hb ↦ by simp only [Set.mem_setOf_eq, add_smul, add_mem ha.out hb.out]
      zero_mem' := by simp only [Set.mem_setOf_eq, zero_smul, zero_mem]
      neg_mem' := by simp only [Set.mem_setOf_eq, neg_smul, neg_mem_iff, imp_self, implies_true]}
    apply IsFiltration.is_sup (F := F) (F_lt := F_lt) S i (fun k hk z hz ↦
      IsFiltration.is_le (VAdd.vadd_lt_vadd_of_lt_of_le hk (Preorder.le_refl j))
      (IsModuleFiltration.smul_mem hz hy)) hx
  smul_F_lt_mem := by
    intro i j x y hx hy
    let S : AddSubgroup M := {
      carrier := {z | x • z ∈ FM_lt (i +ᵥ j)}
      add_mem' := fun ha hb ↦ by simp only [Set.mem_setOf_eq, smul_add, add_mem ha.out hb.out]
      zero_mem' := by simp only [Set.mem_setOf_eq, smul_zero, zero_mem]
      neg_mem' := by simp only [Set.mem_setOf_eq, smul_neg, neg_mem_iff, imp_self, implies_true]}
    apply IsFiltration.is_sup (F := FM) (F_lt := FM_lt) S j (fun k hk z hz ↦
      IsFiltration.is_le (VAdd.vadd_lt_vadd_of_le_of_lt (Preorder.le_refl i) hk)
      (IsModuleFiltration.smul_mem hx hz)) hy

variable [IsRingFiltration F F_lt] (FM : ιM → σM) (FM_lt : outParam <| ιM → σM)

/--The scalar multiplication `F i → FM j → FM (i +ᵥ j)` defined as
the scalar multiplication of its value. -/
def IsModuleFiltration.hSMul [IsModuleFiltration F F_lt FM FM_lt] (i : ι) (j : ιM)
    (x : F i) (y : FM j) : FM (i +ᵥ j) where
  val := x.1 • y
  property := by
    simp [IsModuleFiltration.smul_mem x.2 y.2]

instance (i : ι) (j : ιM) [IsModuleFiltration F F_lt FM FM_lt] :
    HSMul (F i) (FM j) (FM (i +ᵥ j)) where
  hSMul := IsModuleFiltration.hSMul F F_lt FM FM_lt i j

variable [hasGSMul F F_lt FM FM_lt]

theorem hasGSMul.mul_equiv_mul {i : ι} {j : ιM} ⦃x₁ x₂ : F i⦄
    (hx : x₁ ≈ x₂) ⦃y₁ y₂ : FM j⦄ (hy : y₁ ≈ y₂) :
    x₁ • y₁ ≈ x₂ • y₂ := by
  simp only [HasEquiv.Equiv, QuotientAddGroup.leftRel_apply, AddSubgroup.mem_addSubgroupOf,
    AddSubgroup.coe_add, NegMemClass.coe_neg, AddMonoidHom.mem_range, AddSubgroupClass.coeSubtype,
    Subtype.exists, exists_prop, exists_eq_right] at hx hy ⊢
  show -(x₁ • y₁).1 + (x₂ • y₂).1 ∈ (FM_lt (i +ᵥ j))
  have eq : - (x₁ • y₁).1 + (x₂ • y₂).1 = ((- x₁ + x₂) : R) • y₁ + (x₂ : R) • (- y₁ + y₂) := by
    simp only [add_smul, neg_smul, smul_add, smul_neg]
    abel
  rw [eq]
  exact add_mem (hasGSMul.F_lt_smul_mem (F := F) (FM := FM) hx y₁.2)
    (hasGSMul.smul_F_lt_mem (F := F) (FM := FM) x₂.2 hy)

/--The scalar multiplication
`GradedPiece F F_lt i → GradedPiece FM FM_lt j → GradedPiece FM FM_lt (i +ᵥ j)`
lifted from the multiplication `F i → FM j → F (i +ᵥ j)`-/
def hasGSMul.gradedSMul {i : ι} {j : ιM} : GradedPiece F F_lt i → GradedPiece FM FM_lt j →
    GradedPiece FM FM_lt (i +ᵥ j) :=
  Quotient.map₂ (· • ·) (hasGSMul.mul_equiv_mul F F_lt FM FM_lt)

instance hSMul {i : ι} {j : ιM}:
    HSMul (GradedPiece F F_lt i) (GradedPiece FM FM_lt j) (GradedPiece FM FM_lt (i +ᵥ j)) where
  hSMul := hasGSMul.gradedSMul F F_lt FM FM_lt

section HEq

lemma GradedPiece.mk_smul {i : ι} {j : ιM} (x : F i)
    (y : FM j) :
    mk F F_lt x • mk FM FM_lt y = mk FM FM_lt (x • y) := rfl

lemma gradedSMul_def {i : ι} {j : ιM} (x : F i)
    (y : FM j) :
    GradedPiece.mk FM FM_lt (IsModuleFiltration.hSMul F F_lt FM FM_lt i j x y) =
    hasGSMul.gradedSMul F F_lt FM FM_lt (GradedPiece.mk F F_lt x) (GradedPiece.mk FM FM_lt y) := rfl

end HEq

namespace gradedSMul

open GradedPiece

instance : GradedMonoid.GSMul (GradedPiece F F_lt) (GradedPiece FM FM_lt) where
  smul := hasGSMul.gradedSMul F F_lt FM FM_lt

section

lemma GradedPiece.HEq_one_smul {i : ιM} (x : GradedPiece FM FM_lt i) :
    HEq ((1 : GradedPiece F F_lt 0) • x) x := by
  let rx := Quotient.out x
  let r1 : F 0 := ⟨1, IsRingFiltration.one_mem⟩
  have : r1.1 • rx.1 = rx.1 := MulAction.one_smul rx.1
  apply HEq_eq_mk_eq FM FM_lt (zero_vadd ι i) this
  · convert (gradedSMul_def F F_lt FM FM_lt r1 rx).symm
    exact (Quotient.out_eq' x).symm
  · exact (Quotient.out_eq' x).symm
  · simp [this]

theorem GradedPiece.smul_add {i : ι} {j : ιM} (a : GradedPiece F F_lt i)
    (b c : GradedPiece FM FM_lt j) : a • (b + c) = a • b + a • c := by
  induction a using Quotient.ind'
  induction b using Quotient.ind'
  induction c using Quotient.ind'
  show Quotient.mk'' _ = Quotient.mk'' _
  rw [Quotient.eq'']
  simp [QuotientAddGroup.leftRel_apply, AddSubgroup.mem_addSubgroupOf]
  rename_i a1 a2 a3
  have : -(a1 • (a2 + a3)).1 + ((a1 • a2).1 + (a1 • a3).1) = 0 := by
    have : -(a1.1 • (a2.1 + a3.1)) + (a1.1 • a2.1 + a1.1 • a3.1) = 0 := by
      simp only [_root_.smul_add, neg_add_rev]
      abel
    rw [← this]
    rfl
  rw [this]
  exact zero_mem (FM_lt (i +ᵥ j))

theorem GradedPiece.add_smul {i : ι} {j : ιM} (a b : GradedPiece F F_lt i)
    (c : GradedPiece FM FM_lt j) : (a + b) • c = a • c + b • c := by
  induction a using Quotient.ind'
  induction b using Quotient.ind'
  induction c using Quotient.ind'
  show Quotient.mk'' _ = Quotient.mk'' _
  rw [Quotient.eq'']
  simp [QuotientAddGroup.leftRel_apply, AddSubgroup.mem_addSubgroupOf]
  rename_i a1 a2 a3
  have : -((a1 + a2) • a3).1 + ((a1 • a3).1 + (a2 • a3).1) = 0 := by
    have : -((a1.1 + a2.1) • a3.1) + (a1.1 • a3.1 + a2.1 • a3.1) = 0 := by
      simp only [_root_.add_smul, neg_add_rev]
      abel
    rw [← this]
    rfl
  rw [this]
  exact zero_mem (FM_lt (i +ᵥ j))

theorem GradedPiece.smul_zero {i : ι} {j : ιM} (a : GradedPiece F F_lt i) :
    a • (0 : GradedPiece FM FM_lt j) = (0 : GradedPiece FM FM_lt (i +ᵥ j)) := by
  rw [← QuotientAddGroup.mk_zero, ← QuotientAddGroup.mk_zero]
  induction a using Quotient.ind'
  show Quotient.mk'' _ = Quotient.mk'' _
  rw [Quotient.eq'']
  simp only [ZeroMemClass.coe_zero, mul_zero, QuotientAddGroup.leftRel_apply, add_zero, neg_mem_iff]
  show (_ : R) • (0 : M) ∈ (FM_lt (i +ᵥ j))
  simpa only [_root_.smul_zero] using zero_mem (FM_lt (i +ᵥ j))

theorem GradedPiece.zero_smul  {i : ι} {j : ιM} (a : GradedPiece FM FM_lt j) :
    (0 : GradedPiece F F_lt i) • a = (0 : GradedPiece FM FM_lt (i +ᵥ j)) := by
  rw [← QuotientAddGroup.mk_zero, ← QuotientAddGroup.mk_zero]
  induction a using Quotient.ind'
  change Quotient.mk'' _ = Quotient.mk'' _
  rw [Quotient.eq'']
  simp only [ZeroMemClass.coe_zero, zero_mul, QuotientAddGroup.leftRel_apply, add_zero, neg_mem_iff]
  show (0 : R) • (_ : M) ∈ (FM_lt (i +ᵥ j))
  simpa only [_root_.zero_smul] using zero_mem (FM_lt (i +ᵥ j))

lemma GradedPiece.HEq_mul_smul [hasGMul F F_lt] {i j : ι} {k : ιM}
    (a : GradedPiece F F_lt i) (b : GradedPiece F F_lt j) (c : GradedPiece FM FM_lt k) :
    HEq ((a * b) • c) (a • (b • c)) := by
  let ra := Quotient.out a
  let rb := Quotient.out b
  let rc := Quotient.out c
  apply HEq_eq_mk_eq FM FM_lt (add_vadd i j k) (mul_smul ra.1 rb.1 rc.1)
  · show (a * b) • c = ⟦(ra * rb) • rc⟧
    convert (gradedSMul_def F F_lt FM FM_lt (ra * rb) rc).symm
    · convert (gradedMul_def F F_lt ra rb).symm
      · exact (Quotient.out_eq' a).symm
      · exact (Quotient.out_eq' b).symm
    · exact (Quotient.out_eq' c).symm
  · show a • (b • c) = ⟦ra • (rb • rc)⟧
    convert (gradedSMul_def F F_lt FM FM_lt ra (rb • rc)).symm
    · exact (Quotient.out_eq' a).symm
    · convert (gradedSMul_def F F_lt FM FM_lt rb rc).symm
      · exact (Quotient.out_eq' b).symm
      · exact (Quotient.out_eq' c).symm

end

@[simp]
lemma fst_smul (a : GradedMonoid (GradedPiece F F_lt)) (b : GradedMonoid (GradedPiece FM FM_lt)) :
    (a • b).fst = a.fst +ᵥ b.fst := rfl

instance [hasGMul F F_lt] : DirectSum.Gmodule (GradedPiece F F_lt) (GradedPiece FM FM_lt) where
  one_smul := fun ⟨i, a⟩ => Sigma.ext (by simp)
    (GradedPiece.HEq_one_smul F F_lt FM FM_lt a)
  mul_smul := fun ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩ => Sigma.ext (by simp [add_vadd i j k])
    (GradedPiece.HEq_mul_smul F F_lt FM FM_lt a b c)
  smul_add := GradedPiece.smul_add F F_lt FM FM_lt
  smul_zero := GradedPiece.smul_zero F F_lt FM FM_lt
  add_smul := GradedPiece.add_smul F F_lt FM FM_lt
  zero_smul := GradedPiece.zero_smul F F_lt FM FM_lt

open DirectSum in
instance [hasGMul F F_lt] [DecidableEq ι] [DecidableEq ιM] :
    Module (⨁ i, GradedPiece F F_lt i) (⨁ i, GradedPiece FM FM_lt i) :=
  Gmodule.module (GradedPiece F F_lt) (GradedPiece FM FM_lt)

end gradedSMul

end hasGSMul

end GradedModule
