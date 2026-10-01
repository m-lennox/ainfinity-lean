module

public import Mathlib
public import AInfinity.Grading
public import AInfinity.GradedLinearAlgebra

@[expose] public section

open CategoryTheory Finset AInfinityTheory

noncomputable section

namespace AInfinityTheory

universe u v w w'
variable {β : Type v} [GradingIndex β]
variable {n : ℕ}

/-- Target degree of the `n`-ary operation `m`. -/
abbrev operationTargetDeg
    (deg : Fin n → β) : β :=
  (∑ i, deg i) + (2 - (n : ℤ))

/-- Target degree of the arity-`n` Stasheff relation. -/
abbrev stasheffTargetDeg
    (deg : Fin n → β) : β :=
  (∑ i, deg i) + (3 - (n : ℤ))

/-- Valid index pairs for an arity-`n` Stasheff summand. -/
abbrev ValidStasheffIndices (n r s : ℕ) : Prop :=
  1 ≤ s ∧ r + s ≤ n

variable {R : Type u} [CommRing R] {Obj : Type w}
variable (Hom : Obj → Obj → β → Type w') [∀ X Y i, AddCommGroup (Hom X Y i)]
  [∀ X Y i, Module R (Hom X Y i)]

/-- The hom space containing the `i`-th morphism of a composable string of objects, in
degree `b`. -/
abbrev ComposableHomType
    (obj : Fin (n + 1) → Obj)
    (i : Fin n)
    (b : β) : Type w' :=
  Hom
    (obj ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
    (obj ⟨i.val + 1, by omega⟩)
    b

variable (R) in
/-- The type of A∞ compositions on a graded quiver `Hom`: for each arity `n ≥ 1` and each
composable string of objects `obj`, a graded multilinear map `mₙ` of degree `2 - n` from the
composable hom spaces to the hom space from `obj 0` to `obj (Fin.last n)`. -/
abbrev AInfinityComposition :=
  {n : ℕ} → [NeZero n] → (obj : Fin (n + 1) → Obj) →
    GradedMultilinearMap R (ComposableHomType Hom obj) (Hom (obj 0) (obj (Fin.last n)))
      (2 - (n : ℤ) : β)

variable (m : AInfinityComposition R Hom)
variable (obj : Fin (n + 1) → Obj) (deg : Fin n → β)
variable (x : ∀ i : Fin n, ComposableHomType Hom obj i (deg i))
variable (r s : ℕ) (hr : r + s ≤ n)

variable (R) in
/-- Transport between graded hom spaces along equalities of the source, target and degree.
This is the three-index form of `LinearEquiv.cast`. -/
def gradedHomCongr
    {X X' Y Y' : Obj}
    {i i' : β}
    (hX : X = X')
    (hY : Y = Y')
    (hi : i = i') :
    Hom X Y i ≃ₗ[R] Hom X' Y' i' := by
  subst hX hY hi
  exact LinearEquiv.refl R _

variable (R) in
omit [GradingIndex β] in
/-- Transport along reflexivity is the identity. -/
@[simp]
lemma gradedHomCongr_refl
    (X Y : Obj)
    (i : β) :
    gradedHomCongr R Hom (rfl : X = X) (rfl : Y = Y) (rfl : i = i) = LinearEquiv.refl R _ :=
  rfl

variable (R) in
omit [GradingIndex β] in
/-- The inverse of a transport is the transport along the reversed equalities. -/
@[simp]
lemma gradedHomCongr_symm
    {X X' Y Y' : Obj}
    {i i' : β}
    (hX : X = X')
    (hY : Y = Y')
    (hi : i = i') :
    (gradedHomCongr R Hom hX hY hi).symm = gradedHomCongr R Hom hX.symm hY.symm hi.symm := by
  subst hX hY hi
  rfl

variable (R) in
omit [GradingIndex β] in
/-- Transporting twice is transporting along the composite equalities. -/
@[simp]
lemma gradedHomCongr_trans
    {X X' X'' Y Y' Y'' : Obj}
    {i i' i'' : β}
    (hX : X = X')
    (hY : Y = Y')
    (hi : i = i')
    (hX' : X' = X'')
    (hY' : Y' = Y'')
    (hi' : i' = i'') :
    (gradedHomCongr R Hom hX hY hi).trans (gradedHomCongr R Hom hX' hY' hi') =
      gradedHomCongr R Hom (hX.trans hX') (hY.trans hY') (hi.trans hi') := by
  subst hX hY hi hX' hY' hi'
  rfl

/-- Helper: degree function for the inner portion of the Stasheff composition. -/
def stasheffDegIn : Fin s → β :=
  fun i => deg ⟨r + i.val, by omega⟩

/-- Helper: inner degree (the degree of the result of the inner multilinear map). -/
def stasheffInnerDeg : β :=
  operationTargetDeg (stasheffDegIn deg r s hr)

/-- Helper: the outer degree function. -/
def stasheffDegOut : Fin (n + 1 - s) → β :=
  fun i =>
    if h1 : i.val < r then
      deg ⟨i.val, by omega⟩
    else if _ : i.val = r then
      stasheffInnerDeg deg r s hr
    else
      deg ⟨i.val + s - 1, by omega⟩

/-- Helper: the inner object string. -/
def stasheffObjIn : Fin (s + 1) → Obj :=
  fun i => obj ⟨r + i.val, by omega⟩

/-- Helper: the outer object string obtained by collapsing the inner block. -/
def stasheffObjOut : Fin ((n + 1 - s) + 1) → Obj :=
  fun i =>
    if h1 : i.val ≤ r then
      obj ⟨i.val, by omega⟩
    else
      obj ⟨i.val + s - 1, by omega⟩

/-- Combine the two operation-degree shifts in a nested Stasheff term. -/
private lemma shift_ofInt_combine {n s : ℕ} (hsn : s ≤ n) :
    ((2 - (s : ℤ)) : β) + (2 - ((n + 1 - s : ℕ) : ℤ)) =
    (3 - (n : ℤ)) := by
  have : 3 - (n : ℤ) = 2 - (s : ℤ) + 2 - ((n + 1 - s : ℕ) : ℤ) := by
    have hle : s ≤ n + 1 := Nat.le_succ_of_le hsn
    rw [Nat.cast_sub hle]
    push_cast
    omega
  norm_cast
  suffices
    Int.subNatNat 2 s + Int.subNatNat 2 (n + 1 - s) = Int.subNatNat 3 n
  by
    rw [this]
  simp only [Int.subNatNat_eq_coe, Nat.cast_ofNat, this]
  symm
  rw [Int.add_sub_assoc]

/-- The finite ranges used in the Stasheff sum produce valid index pairs. -/
lemma validStasheffIndices_of_mem_ranges
    {r s : ℕ}
    (hr : r ∈ Finset.range (n + 1))
    (hs : s ∈ Finset.Ico 1 (n - r + 1)) :
    ValidStasheffIndices n r s := by
  rcases Finset.mem_range.mp hr with hr
  rcases Finset.mem_Ico.mp hs with ⟨hs₁, hs₂⟩
  refine ⟨hs₁, ?_⟩
  omega

/-- Summing the outer degrees recovers the original total degree plus the inner shift. -/
lemma stasheffDegOut_sum_core :
    (∑ i : Fin (n + 1 - s), stasheffDegOut deg r s hr i) =
    (∑ i : Fin n, deg i) + (2 - (s : ℤ)) := by
  unfold stasheffDegOut
  rw [
    show (Finset.univ : Finset (Fin (n + 1 - s))) =
        Finset.univ.filter (fun i : Fin (n + 1 - s) => i.val < r) ∪
          Finset.univ.filter (fun i : Fin (n + 1 - s) => i.val = r) ∪
          Finset.univ.filter (fun i : Fin (n + 1 - s) => i.val > r) from ?_,
    Finset.sum_union,
    Finset.sum_union
  ]
  · rw [
      show Finset.univ.filter (fun i : Fin (n + 1 - s) => (i : ℕ) < r) =
          Finset.image (fun i : Fin r => ⟨i, by omega⟩) Finset.univ from ?_,
      show Finset.univ.filter (fun i : Fin (n + 1 - s) => (i : ℕ) = r) =
          {⟨r, by omega⟩} from ?_,
      show Finset.univ.filter (fun i : Fin (n + 1 - s) => (i : ℕ) > r) =
          Finset.image
            (fun i : Fin (n - r - s) => ⟨r + 1 + i, by omega⟩)
            Finset.univ from ?_
    ]
    · rw [Finset.sum_image, Finset.sum_image] <;> norm_num
      · rw [
          show (Finset.univ : Finset (Fin n)) =
              Finset.image
                  (fun i : Fin r => ⟨i, by linarith [Fin.is_lt i]⟩)
                  Finset.univ ∪
                Finset.image
                  (fun i : Fin s => ⟨r + i, by linarith [Fin.is_lt i]⟩)
                  Finset.univ ∪
                Finset.image
                  (fun i : Fin (n - r - s) => ⟨r + s + i, by omega⟩)
                  Finset.univ from ?_,
          Finset.sum_union,
          Finset.sum_union
        ]
        · rw [Finset.sum_image, Finset.sum_image, Finset.sum_image] <;> norm_num
          · unfold stasheffInnerDeg
            unfold stasheffDegIn
            unfold operationTargetDeg
            ring_nf
            norm_cast
            simp only [← Int.coe_castAddHom, Int.subNatNat_eq_coe, Nat.cast_ofNat]
            grind
          · exact fun i j h => by simpa [Fin.ext_iff] using h
          · exact fun i j h => by simpa [Fin.ext_iff] using h
          · exact fun i j h => by simpa [Fin.ext_iff] using h
        · norm_num [Finset.disjoint_left]
          grind
        · norm_num [Finset.disjoint_right]
          grind
        · ext ⟨i, hi⟩
          simp only
            [mem_univ, union_assoc, mem_union, mem_image, Fin.mk.injEq, true_and,
              true_iff]
          by_cases hi' : i < r
          · exact Or.inl ⟨⟨i, by linarith⟩, rfl⟩
          · by_cases hi'' : i < r + s
            · exact Or.inr <| Or.inl <|
                ⟨⟨i - r, by omega⟩, by
                  simp +decide [Nat.add_sub_of_le (le_of_not_gt hi')]
                ⟩
            · exact Or.inr <| Or.inr <| ⟨⟨i - (r + s), by omega⟩, by
                norm_num
                omega
              ⟩
      · exact fun i j h => by simpa [Fin.ext_iff] using h
      · exact fun i j h => by simpa [Fin.ext_iff] using h
    · apply Finset.ext
      intro i
      simp only [gt_iff_lt, mem_filter, mem_univ, true_and, mem_image]
      exact
        ⟨
          (fun hi => ⟨⟨i - (r + 1), by omega⟩, by
            erw [Fin.ext_iff]
            norm_num
            omega
          ⟩),
          by
            rintro ⟨a, rfl⟩
            exact
              Nat.lt_of_lt_of_le
                (by simp +arith +decide)
                (Nat.le_add_right _ _)
        ⟩
    · ext ⟨i, hi⟩
      aesop
    · ext ⟨i, hi⟩
      simp only [mem_filter, mem_univ, true_and, mem_image, Fin.mk.injEq]
      exact
        ⟨
          (fun hi' => ⟨⟨i, by omega⟩, rfl⟩),
          fun ⟨a, ha⟩ => by linarith [Fin.is_lt a]
        ⟩
  · exact Finset.disjoint_filter.mpr fun _ _ _ _ => by linarith
  · simp +contextual only [gt_iff_lt, disjoint_left, mem_union, mem_filter, mem_univ, true_and,
    not_lt]
    exact fun a ha => ha.elim (fun ha => le_of_lt ha) fun ha => ha.le
  · ext i
    cases lt_trichotomy i.val r <;> aesop

/-- The outer operation has the Stasheff target degree. -/
lemma stasheffDegOut_sum :
    (∑ i : Fin (n + 1 - s), stasheffDegOut deg r s hr i) +
      (2 - ((n + 1 - s : ℕ) : ℤ)) =
    stasheffTargetDeg deg := by
  rw [stasheffDegOut_sum_core deg r s hr, add_assoc,
      shift_ofInt_combine (by omega : s ≤ n)]

/-- The middle outer degree is the degree of the output of the inner operation. -/
lemma stasheffDegOut_of_eq
    (i : Fin (n + 1 - s))
    (heq : i.val = r) :
    stasheffDegOut deg r s hr i = stasheffInnerDeg deg r s hr := by
  simp [stasheffDegOut, heq]

/-! From here on, `Hom`, `obj` and `deg` are inferred from the operations `m` and the inputs
`x`; declarations that take neither bind them explicitly. -/

variable {Hom obj deg}

/-- Rewriting the degree function and transporting each input does not change the value of `m`. -/
lemma multilinearFamily_eq_of_deg_eq
    [NeZero n]
    {deg deg' : Fin n → β}
    (hdeg : deg = deg')
    (x : ∀ i : Fin n, ComposableHomType Hom obj i (deg i))
    {d : β}
    (hd : operationTargetDeg deg = d)
    (hd' : operationTargetDeg deg' = d) :
    m obj deg' d hd' (fun i => gradedHomCongr R Hom rfl rfl (congrFun hdeg i) (x i)) =
      m obj deg d hd x := by
  subst hdeg
  rfl

/-- Helper: the input tuple for the inner operation in a Stasheff term. -/
def indexedStasheffXIn :
    ∀ i : Fin s,
      ComposableHomType Hom (stasheffObjIn obj r s hr) i (stasheffDegIn deg r s hr i) :=
  fun i => x ⟨r + i.val, by omega⟩

omit [GradingIndex β] [∀ X Y i, AddCommGroup (Hom X Y i)] in
/-- Evaluating the inner input tuple just picks out the corresponding original input. -/
lemma indexedStasheffXIn_apply
    (i : Fin s) :
    indexedStasheffXIn x r s hr i = x ⟨r + i.val, by omega⟩ := by
  simp [indexedStasheffXIn, ComposableHomType, stasheffObjIn, stasheffDegIn]

/-- Helper: the inner value appearing in a Stasheff term, in any degree `d` equal to the
inner degree. -/
def indexedStasheffInner
    (hs : 1 ≤ s)
    (d : β)
    (hd : stasheffInnerDeg deg r s hr = d) :
    Hom (stasheffObjIn obj r s hr 0) (stasheffObjIn obj r s hr (Fin.last s)) d :=
  letI : NeZero s := ⟨by omega⟩
  m (stasheffObjIn obj r s hr) (stasheffDegIn deg r s hr) d hd
    (indexedStasheffXIn x r s hr)

/-- Helper: the middle index in the outer tuple of a Stasheff term. -/
def indexedStasheffMiddleIndex : Fin (n + 1 - s) :=
  ⟨r, by omega⟩

variable (R Hom obj deg) in
/-- Before the inserted block, the original input space is identified with the outer input
space. -/
def indexedStasheffXOutEquivOfLt
    (i : Fin (n + 1 - s))
    (hlt : i.val < r) :
    ComposableHomType Hom obj ⟨i.val, by omega⟩ (deg ⟨i.val, by omega⟩) ≃ₗ[R]
      ComposableHomType Hom (stasheffObjOut obj r s hr) i (stasheffDegOut deg r s hr i) := by
  refine gradedHomCongr R Hom ?_ ?_ ?_ <;>
    simp [stasheffObjOut, stasheffDegOut, hlt, Nat.le_of_lt hlt]

variable (R Hom obj) in
/-- At the inserted block, the space of the inner output is identified with the outer middle
input space, in any degree `d`. -/
def indexedStasheffXOutEquivOfEq
    (i : Fin (n + 1 - s))
    (heq : i.val = r)
    (d : β) :
    Hom (stasheffObjIn obj r s hr 0) (stasheffObjIn obj r s hr (Fin.last s)) d ≃ₗ[R]
      ComposableHomType Hom (stasheffObjOut obj r s hr) i d := by
  refine gradedHomCongr R Hom ?_ ?_ rfl <;>
    simp [stasheffObjIn, stasheffObjOut, heq]

variable (R Hom obj deg) in
/-- After the inserted block, the shifted original input space is identified with the outer
input space. -/
def indexedStasheffXOutEquivOfGt
    (i : Fin (n + 1 - s))
    (hlt : ¬ i.val < r)
    (heq : i.val ≠ r) :
    ComposableHomType Hom obj ⟨i.val + s - 1, by omega⟩ (deg ⟨i.val + s - 1, by omega⟩) ≃ₗ[R]
      ComposableHomType Hom (stasheffObjOut obj r s hr) i (stasheffDegOut deg r s hr i) := by
  have hgt : ¬ i.val ≤ r := by omega
  have hsucc : i.val + s - 1 + 1 = i.val + s := by omega
  refine gradedHomCongr R Hom ?_ ?_ ?_ <;>
    simp [stasheffObjOut, stasheffDegOut, hlt, heq, hgt, hsucc]

/-- Helper: the input tuple for the outer operation in a Stasheff term. -/
def indexedStasheffXOut
    (hs : 1 ≤ s) :
    ∀ i : Fin (n + 1 - s),
      ComposableHomType Hom (stasheffObjOut obj r s hr) i (stasheffDegOut deg r s hr i) :=
  fun i =>
    if hlt : i.val < r then
      indexedStasheffXOutEquivOfLt R Hom obj deg r s hr i hlt (x ⟨i.val, by omega⟩)
    else if heq : i.val = r then
      indexedStasheffXOutEquivOfEq R Hom obj r s hr i heq _
        (indexedStasheffInner m x r s hr hs _
          (stasheffDegOut_of_eq deg r s hr i heq).symm)
    else
      indexedStasheffXOutEquivOfGt R Hom obj deg r s hr i hlt heq
        (x ⟨i.val + s - 1, by omega⟩)

/-- Before the inserted block, the outer input tuple agrees with the original inputs. -/
lemma indexedStasheffXOut_apply_of_lt
    (hs : 1 ≤ s)
    (i : Fin (n + 1 - s))
    (hlt : i.val < r) :
    indexedStasheffXOut m x r s hr hs i =
      indexedStasheffXOutEquivOfLt R Hom obj deg r s hr i hlt (x ⟨i.val, by omega⟩) := by
  simp only [indexedStasheffXOut, dif_pos hlt]

/-- After the inserted block, the outer input tuple agrees with the shifted original inputs. -/
lemma indexedStasheffXOut_apply_of_gt
    (hs : 1 ≤ s)
    (i : Fin (n + 1 - s))
    (hgt : r < i.val) :
    indexedStasheffXOut m x r s hr hs i =
      indexedStasheffXOutEquivOfGt R Hom obj deg r s hr i (by omega) (by omega)
        (x ⟨i.val + s - 1, by omega⟩) := by
  simp only [indexedStasheffXOut, dif_neg (show ¬ i.val < r by omega),
    dif_neg (show i.val ≠ r by omega)]

/-- Helper: positivity of the outer arity in a Stasheff term. -/
lemma indexedStasheffOuterArity_pos
    {n : ℕ}
    {r s : ℕ}
    (hr : r + s ≤ n) :
    0 < n + 1 - s := by
  omega

/-- Helper: the outer value appearing in a Stasheff term, in any degree `d` equal to the
degree of the outer operation. -/
def indexedStasheffOuter
    (hs : 1 ≤ s)
    (d : β)
    (hd : operationTargetDeg (stasheffDegOut deg r s hr) = d) :
    Hom (stasheffObjOut obj r s hr 0) (stasheffObjOut obj r s hr (Fin.last (n + 1 - s))) d :=
  letI : NeZero (n + 1 - s) := ⟨Nat.ne_of_gt (indexedStasheffOuterArity_pos hr)⟩
  m (stasheffObjOut obj r s hr) (stasheffDegOut deg r s hr) d hd
    (indexedStasheffXOut m x r s hr hs)

variable (R Hom obj) in
/-- Helper: the identification of the outer target space with the final Stasheff target space,
in any degree `d`. -/
def indexedStasheffTargetEquiv
    (d : β) :
    Hom (stasheffObjOut obj r s hr 0) (stasheffObjOut obj r s hr (Fin.last (n + 1 - s))) d ≃ₗ[R]
      Hom (obj 0) (obj (Fin.last n)) d :=
  gradedHomCongr R Hom (by simp [stasheffObjOut])
    (by
      simp only [stasheffObjOut, Fin.last, show ¬ n + 1 - s ≤ r by omega, ↓reduceDIte]
      congr
      omega)
    rfl

/-- A generic Stasheff term builder for object-indexed A∞ operations, in any degree `d` equal
to the Stasheff target degree. -/
def indexedStasheffTerm
    (hs : 1 ≤ s)
    (d : β)
    (hd : stasheffTargetDeg deg = d) :
    Hom (obj 0) (obj (Fin.last n)) d :=
  indexedStasheffTargetEquiv R Hom obj r s hr d
    (indexedStasheffOuter m x r s hr hs d
      ((stasheffDegOut_sum deg r s hr).trans hd))

/-- The middle outer input is the transported inner output. -/
lemma indexedStasheffXOut_middle_eq
    (hs : 1 ≤ s) :
    indexedStasheffXOut m x r s hr hs (indexedStasheffMiddleIndex r s hr) =
      indexedStasheffXOutEquivOfEq R Hom obj r s hr (indexedStasheffMiddleIndex r s hr) rfl _
        (indexedStasheffInner m x r s hr hs _
          (stasheffDegOut_of_eq deg r s hr (indexedStasheffMiddleIndex r s hr) rfl).symm) := by
  simp [indexedStasheffXOut, indexedStasheffMiddleIndex]

/-- The middle outer input vanishes whenever the inner output vanishes. -/
lemma indexedStasheffXOut_middle_eq_zero_of_inner_eq_zero
    (hs : 1 ≤ s)
    (hinner : ∀ d hd, indexedStasheffInner m x r s hr hs d hd = 0) :
    indexedStasheffXOut m x r s hr hs (indexedStasheffMiddleIndex r s hr) = 0 := by
  rw [indexedStasheffXOut_middle_eq, hinner, map_zero]

/-- The inner value vanishes if the inner multilinear map itself vanishes. -/
lemma indexedStasheffInner_eq_zero_of_map_eq_zero
    (hs : 1 ≤ s)
    (hm : ∀ d hd,
      @m s ⟨by omega⟩ (stasheffObjIn obj r s hr) (stasheffDegIn deg r s hr) d hd = 0)
    (d : β)
    (hd : stasheffInnerDeg deg r s hr = d) :
    indexedStasheffInner m x r s hr hs d hd = 0 := by
  simp [indexedStasheffInner, hm]

/-- The outer value vanishes if the outer multilinear map itself vanishes. -/
lemma indexedStasheffOuter_eq_zero_of_map_eq_zero
    (hs : 1 ≤ s)
    (hm : ∀ d hd,
      @m (n + 1 - s) ⟨Nat.ne_of_gt (indexedStasheffOuterArity_pos hr)⟩
        (stasheffObjOut obj r s hr) (stasheffDegOut deg r s hr) d hd = 0)
    (d : β)
    (hd : operationTargetDeg (stasheffDegOut deg r s hr) = d) :
    indexedStasheffOuter m x r s hr hs d hd = 0 := by
  simp [indexedStasheffOuter, hm]

/-- The outer value vanishes whenever the inserted inner output vanishes. -/
lemma indexedStasheffOuter_eq_zero_of_inner_eq_zero
    (hs : 1 ≤ s)
    (hinner : ∀ d hd, indexedStasheffInner m x r s hr hs d hd = 0)
    (d : β)
    (hd : operationTargetDeg (stasheffDegOut deg r s hr) = d) :
    indexedStasheffOuter m x r s hr hs d hd = 0 := by
  dsimp [indexedStasheffOuter]
  letI : NeZero (n + 1 - s) := ⟨Nat.ne_of_gt (indexedStasheffOuterArity_pos hr)⟩
  exact MultilinearMap.map_coord_zero
    (m (stasheffObjOut obj r s hr) (stasheffDegOut deg r s hr) d hd)
    (indexedStasheffMiddleIndex r s hr)
    (indexedStasheffXOut_middle_eq_zero_of_inner_eq_zero m x r s hr hs hinner)

/-- The final transported Stasheff term vanishes exactly when the outer value vanishes. -/
lemma indexedStasheffTerm_eq_zero_iff_outer_eq_zero
    (hs : 1 ≤ s)
    (d : β)
    (hd : stasheffTargetDeg deg = d) :
    indexedStasheffTerm m x r s hr hs d hd = 0 ↔
      indexedStasheffOuter m x r s hr hs d
        ((stasheffDegOut_sum deg r s hr).trans hd) = 0 :=
  (indexedStasheffTargetEquiv R Hom obj r s hr d).map_eq_zero_iff

/-- The final Stasheff term vanishes if the outer multilinear map vanishes. -/
lemma indexedStasheffTerm_eq_zero_of_outer_map_eq_zero
    (hs : 1 ≤ s)
    (hm : ∀ d hd,
      @m (n + 1 - s) ⟨Nat.ne_of_gt (indexedStasheffOuterArity_pos hr)⟩
        (stasheffObjOut obj r s hr) (stasheffDegOut deg r s hr) d hd = 0)
    (d : β)
    (hd : stasheffTargetDeg deg = d) :
    indexedStasheffTerm m x r s hr hs d hd = 0 :=
  (indexedStasheffTerm_eq_zero_iff_outer_eq_zero m x r s hr hs d hd).2
    (indexedStasheffOuter_eq_zero_of_map_eq_zero m x r s hr hs hm _ _)

/-- The final Stasheff term vanishes if the inner multilinear map vanishes. -/
lemma indexedStasheffTerm_eq_zero_of_inner_map_eq_zero
    (hs : 1 ≤ s)
    (hm : ∀ d hd,
      @m s ⟨by omega⟩ (stasheffObjIn obj r s hr) (stasheffDegIn deg r s hr) d hd = 0)
    (d : β)
    (hd : stasheffTargetDeg deg = d) :
    indexedStasheffTerm m x r s hr hs d hd = 0 :=
  (indexedStasheffTerm_eq_zero_iff_outer_eq_zero m x r s hr hs d hd).2
    (indexedStasheffOuter_eq_zero_of_inner_eq_zero m x r s hr hs
      (indexedStasheffInner_eq_zero_of_map_eq_zero m x r s hr hs hm) _ _)

variable (deg) in
/-- The sign parity for the `(r,s)` Stasheff term:
    `sign(deg(r+s)) + ⋯ + sign(deg(n-1)) - (n-r-s)` in `ZMod 2`. -/
def stasheffSignParity : ZMod 2 :=
  (∑ i : Fin (n - r - s), parity (deg ⟨r + s + i.val, by omega⟩)) -
    ((n - r - s : ℕ) : ZMod 2)

variable (deg) in
/-- The sign `(-1)^(|a_{r+s+1}| + ⋯ + |a_n| - t)` as an integer,
    for a valid Stasheff index pair. -/
def stasheffSign : ℤ :=
  (-1) ^ (stasheffSignParity deg r s hr).val

/-- The full Stasheff sum in arity `n`, with Koszul signs, in any degree `d` equal to the
Stasheff target degree. -/
def indexedStasheffSum
    (d : β)
    (hd : stasheffTargetDeg deg = d) :
    Hom (obj 0) (obj (Fin.last n)) d :=
  ∑ r ∈ (Finset.range (n + 1)).attach,
    ∑ s ∈ (Finset.Ico 1 (n - r.1 + 1)).attach,
      let h : ValidStasheffIndices n r.1 s.1 :=
        validStasheffIndices_of_mem_ranges (n := n) r.2 s.2
      (stasheffSign deg r.1 s.1 h.2) •
        (indexedStasheffTerm m x r.1 s.1 h.2 h.1 d hd)

/-- The Stasheff identities for object-indexed A∞ operations. -/
def indexedSatisfiesStasheff : Prop :=
  ∀ (n : ℕ) [NeZero n] (obj : Fin (n + 1) → Obj) (deg : Fin n → β)
    (x : ∀ i : Fin n, ComposableHomType Hom obj i (deg i)) (d : β)
    (hd : stasheffTargetDeg deg = d),
    indexedStasheffSum m x d hd = 0

end AInfinityTheory
