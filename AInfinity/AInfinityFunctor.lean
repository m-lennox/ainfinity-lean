/-
Copyright (c) 2026 Annie Yao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Annie Yao, Marco David, Jason Dong, Zhan Shi
-/
module

public import AInfinity.AInfinityCategory
public import Mathlib.Combinatorics.Enumerative.Composition

/-! # A∞-functors

An `A∞`-functor `F : A → B` between `A∞`-categories consists of a map on objects together with,
for each `n ≥ 1`, a multilinear map
`φₙ : Hom(X₀, X₁) ⊗ ⋯ ⊗ Hom(Xₙ₋₁, Xₙ) → Hom(F X₀, F Xₙ)` of degree `1 - n`, satisfying the
`A∞`-functor equations
`∑_{r + s + t = n, s ≥ 1} (-1)^(‖a_{r+s+1}‖ + ⋯ + ‖a_n‖)
  φ_{r+1+t}(a_1, …, a_r, m^A_s(a_{r+1}, …, a_{r+s}), a_{r+s+1}, …, a_n)
= ∑_{k ≥ 1} ∑_{i₁ + ⋯ + iₖ = n} m^B_k(φ_{i₁}(a_1, …, a_{i₁}), …, φ_{iₖ}(a_{n-iₖ+1}, …, a_n))`.

The sign on the left is the Koszul sign `stasheffSign` of the Stasheff identities. There is no
sign on the right: in reduced degrees `‖a‖ = |a| - 1` every `φᵢ` has degree `0`, so no Koszul
sign arises from moving it past the inputs (compare [Seidel, *Fukaya categories and
Picard–Lefschetz theory*, (1.6)]).

The source and target may be graded by different grading types `β_A` and `β_B`; the functor then
carries a homomorphism `β_A →+ β_B` compatible with the integer shifts and the Koszul signs.

## Main definitions

* `AInfinityTheory.AInfinityFunctorData β_A β_B R ObjA ObjB`: a map on objects, a grading
  homomorphism and functor components `φₙ`, not yet subject to any relations.
* `AInfinityTheory.AInfinityFunctorData.functorLHSSum`: the left-hand side of the arity-`n`
  functor equation.
* `AInfinityTheory.AInfinityFunctorData.functorRHSSum`: the right-hand side of the arity-`n`
  functor equation.
* `AInfinityTheory.AInfinityFunctorData.SatisfiesFunctorEquations`: the functor equations in
  every arity.
* `AInfinityTheory.AInfinityFunctor β_A β_B R ObjA ObjB`: an `A∞`-functor between
  `A∞`-categories.

## Implementation notes

The component `φₙ` is a `GradedMultilinearMap` of degree `shift (1 - n)` in the source grading,
into the pullback `b ↦ Hom(F X₀, F Xₙ)(gradingHom b)` of the target hom spaces. Both sides of
the functor equation are stated pointwise on a composable string of inputs, in degree
`gradingHom d` for any `d` equal to the degree of `mₙ`, as for `indexedStasheffSum`. Changes of
objects are transported with `homCongr`. The ordered decompositions `i₁ + ⋯ + iₖ = n` on the
right-hand side are Mathlib's `Composition n`.
-/

@[expose] public section

noncomputable section

namespace AInfinityTheory

open GradedLinearQuiver

variable {n : ℕ}

section Degrees

variable {β : Type*} [AddCommGroup β] [GradingType β]

/-- Target degree of the `n`-ary functor component `φₙ`, which has degree `1 - n`. -/
abbrev functorTargetDeg (deg : Fin n → β) : β :=
  (∑ i, deg i) + shift (1 - (n : ℤ))

/-- The `n`-ary operation `mₙ` has degree one more than the `n`-ary functor component `φₙ`. -/
lemma operationTargetDeg_eq_functorTargetDeg_add_shift_one (deg : Fin n → β) :
    operationTargetDeg deg = functorTargetDeg deg + shift 1 := by
  sorry

/-- In an `(r, s, t)` term of the left-hand side of the functor equation, the outer functor
component lands in the degree of `mₙ`. -/
lemma functorTargetDeg_stasheffDegOut (deg : Fin n → β) (r s t : ℕ) (ht : r + s + t = n) :
    functorTargetDeg (stasheffDegOut deg r s t ht) = operationTargetDeg deg := by
  sorry

/-- Applying functor components to the blocks of a composition `c` of `n` and then the
`c.length`-ary operation lands in the degree of `mₙ`. -/
lemma operationTargetDeg_functorTargetDeg_embedding (deg : Fin n → β) (c : Composition n) :
    operationTargetDeg (fun l ↦ functorTargetDeg fun j ↦ deg (c.embedding l j)) =
      operationTargetDeg deg := by
  sorry

end Degrees

section CompositionBlock

variable {Obj : Type*} (obj : Fin (n + 1) → Obj) (c : Composition n) (l : Fin c.length)

/-- The object string `obj iₗ, …, obj (iₗ + c.blocksFun l)` of the `l`-th block of a composition
`c` of `n`, where `iₗ = c.sizeUpTo l` is the start of the block. -/
def compositionBlockObj : Fin (c.blocksFun l + 1) → Obj :=
  fun i ↦ obj ((i.natAdd (c.sizeUpTo l)).castLE (by
    have := c.sizeUpTo_succ' l
    have := c.sizeUpTo_le ((l : ℕ) + 1)
    omega))

/-- The `l`-th block of a composition starts at the `l`-th boundary. -/
@[simp]
lemma compositionBlockObj_zero :
    compositionBlockObj obj c l 0 = obj (c.boundary l.castSucc) := by
  sorry

/-- The `l`-th block of a composition ends at the `(l + 1)`-st boundary. -/
@[simp]
lemma compositionBlockObj_last :
    compositionBlockObj obj c l (Fin.last (c.blocksFun l)) = obj (c.boundary l.succ) := by
  sorry

end CompositionBlock

/-- The data of an `A∞`-functor between graded `R`-linear quivers: a map on objects, a
homomorphism of grading types and, for each `n ≥ 1`, a functor component `φₙ` of degree `1 - n`.
No relations are imposed. -/
structure AInfinityFunctorData (β_A β_B : Type*) [AddCommGroup β_A] [GradingType β_A]
    [AddCommGroup β_B] [GradingType β_B] (R : Type*) [CommRing R] (ObjA ObjB : Type*)
    [GradedLinearQuiver β_A R ObjA] [GradedLinearQuiver β_B R ObjB] where
  /-- The map on objects. -/
  objMap : ObjA → ObjB
  /-- The translation of degrees from the source grading to the target grading. -/
  gradingHom : β_A →+ β_B
  /-- The grading homomorphism preserves the integer degree shifts. -/
  map_shift : ∀ k : ℤ, gradingHom (shift k) = shift k
  /-- The grading homomorphism preserves the Koszul signs. -/
  map_sign : ∀ b : β_A, sign (gradingHom b) = sign b
  /-- The functor components `φₙ`, of degree `1 - n`, landing in the hom spaces of the target
  in the translated degrees. -/
  phi : {n : ℕ} → [NeZero n] → (obj : Fin (n + 1) → ObjA) →
    GradedMultilinearMap R (ComposableHomType R (β := β_A) obj)
      (fun b : β_A ↦ (objMap (obj 0) →ᵍ[R] objMap (obj (Fin.last n))) (gradingHom b))
      (shift (1 - (n : ℤ)))

namespace AInfinityFunctorData

variable {β_A β_B : Type*} [AddCommGroup β_A] [GradingType β_A] [AddCommGroup β_B]
  [GradingType β_B] {R : Type*} [CommRing R] {ObjA ObjB : Type*}
  [GradedLinearQuiver β_A R ObjA] [GradedLinearQuiver β_B R ObjB]
variable (m_A : AInfinityComposition β_A R ObjA) (m_B : AInfinityComposition β_B R ObjB)
variable (F : AInfinityFunctorData β_A β_B R ObjA ObjB)
variable {obj : Fin (n + 1) → ObjA} {deg : Fin n → β_A}
variable (x : ∀ i : Fin n, ComposableHomType R obj i (deg i))

/-- The grading homomorphism commutes with taking the degree of an operation. -/
lemma operationTargetDeg_gradingHom {k : ℕ} (b : Fin k → β_A) :
    operationTargetDeg (fun i ↦ F.gradingHom (b i)) = F.gradingHom (operationTargetDeg b) := by
  sorry

/-! ### The left-hand side of the functor equation -/

/-- The `(r, s, t)` term `φ_{r+1+t}(a_1, …, a_r, m^A_s(a_{r+1}, …, a_{r+s}), a_{r+s+1}, …, a_n)`
of the left-hand side of the functor equation, in degree `F.gradingHom d` for any `d` equal to
the degree of `mₙ`. -/
def functorLHSTerm (r s t : ℕ) (ht : r + s + t = n) (hs : 1 ≤ s) (d : β_A)
    (hd : operationTargetDeg deg = d) :
    (F.objMap (obj 0) →ᵍ[R] F.objMap (obj (Fin.last n))) (F.gradingHom d) :=
  letI : NeZero (r + 1 + t) := ⟨by omega⟩
  homCongr R (congrArg F.objMap (stasheffObjOut_zero obj r s t ht))
    (congrArg F.objMap (stasheffObjOut_last obj r s t ht)) rfl
    (F.phi (stasheffObjOut obj r s t ht) (stasheffDegOut deg r s t ht) d
      ((functorTargetDeg_stasheffDegOut deg r s t ht).trans hd)
      (indexedStasheffXOut m_A x r s t ht hs))

/-- The left-hand side of the arity-`n` functor equation, with the Koszul signs of the Stasheff
identities, in degree `F.gradingHom d` for any `d` equal to the degree of `mₙ`. The term indexed
by `(r, s)` has `t = n - r - s` trailing inputs. -/
def functorLHSSum (d : β_A) (hd : operationTargetDeg deg = d) :
    (F.objMap (obj 0) →ᵍ[R] F.objMap (obj (Fin.last n))) (F.gradingHom d) :=
  ∑ r : Finset.range (n + 1),
    ∑ s : Finset.Ico 1 (n - r.1 + 1),
      have h : ValidStasheffIndices n r.1 s.1 :=
        validStasheffIndices_of_mem_ranges (n := n) r.2 s.2
      have ht : r.1 + s.1 + (n - r.1 - s.1) = n := by
        rw [Nat.sub_sub]
        exact Nat.add_sub_of_le h.2
      (stasheffSign deg r.1 s.1 (n - r.1 - s.1) ht) •
        (functorLHSTerm m_A F x r.1 s.1 (n - r.1 - s.1) ht h.1 d hd)

/-! ### The right-hand side of the functor equation -/

/-- The output `φ_{iₗ}` of the `l`-th block of a composition `c = (i₁, …, iₖ)` of `n`, as the
`l`-th input of the outer operation `m^B_k`. -/
def functorRHSBlock (c : Composition n) (l : Fin c.length) :
    ComposableHomType R (fun k ↦ F.objMap (obj (c.boundary k))) l
      (F.gradingHom (functorTargetDeg fun j ↦ deg (c.embedding l j))) :=
  letI : NeZero (c.blocksFun l) := ⟨Nat.one_le_iff_ne_zero.mp (c.one_le_blocksFun l)⟩
  homCongr R (congrArg F.objMap (compositionBlockObj_zero obj c l))
    (congrArg F.objMap (compositionBlockObj_last obj c l)) rfl
    (F.phi (compositionBlockObj obj c l) (fun j ↦ deg (c.embedding l j)) _ rfl
      fun j ↦ x (c.embedding l j))

/-- The term `m^B_k(φ_{i₁}(a_1, …, a_{i₁}), …, φ_{iₖ}(a_{n-iₖ+1}, …, a_n))` of the right-hand
side of the functor equation indexed by a composition `c = (i₁, …, iₖ)` of `n`, in degree
`F.gradingHom d` for any `d` equal to the degree of `mₙ`. -/
def functorRHSTerm [NeZero n] (c : Composition n) (d : β_A) (hd : operationTargetDeg deg = d) :
    (F.objMap (obj 0) →ᵍ[R] F.objMap (obj (Fin.last n))) (F.gradingHom d) :=
  letI : NeZero c.length := ⟨(c.length_pos_of_pos (NeZero.pos n)).ne'⟩
  homCongr R (congrArg (fun k ↦ F.objMap (obj k)) c.boundary_zero)
    (congrArg (fun k ↦ F.objMap (obj k)) c.boundary_last) rfl
    (m_B (fun k ↦ F.objMap (obj (c.boundary k)))
      (fun l ↦ F.gradingHom (functorTargetDeg fun j ↦ deg (c.embedding l j))) (F.gradingHom d)
      ((F.operationTargetDeg_gradingHom
          fun l ↦ functorTargetDeg fun j ↦ deg (c.embedding l j)).trans
        (congrArg F.gradingHom ((operationTargetDeg_functorTargetDeg_embedding deg c).trans hd)))
      (functorRHSBlock F x c))

/-- The right-hand side of the arity-`n` functor equation, summed over all compositions of `n`,
in degree `F.gradingHom d` for any `d` equal to the degree of `mₙ`. -/
def functorRHSSum [NeZero n] (d : β_A) (hd : operationTargetDeg deg = d) :
    (F.objMap (obj 0) →ᵍ[R] F.objMap (obj (Fin.last n))) (F.gradingHom d) :=
  ∑ c : Composition n, functorRHSTerm m_B F x c d hd

/-- The `A∞`-functor equations: in every arity `n ≥ 1`, the left-hand side and the right-hand
side of the functor equation agree on every composable string of inputs. -/
def SatisfiesFunctorEquations : Prop :=
  ∀ (n : ℕ) [NeZero n] (obj : Fin (n + 1) → ObjA) (deg : Fin n → β_A)
    (x : ∀ i : Fin n, ComposableHomType R obj i (deg i)) (d : β_A)
    (hd : operationTargetDeg deg = d),
    functorLHSSum m_A F x d hd = functorRHSSum m_B F x d hd

end AInfinityFunctorData

/-- An `A∞`-functor between `A∞`-categories: `A∞`-functor data satisfying the functor
equations. -/
structure AInfinityFunctor (β_A β_B : Type*) [AddCommGroup β_A] [GradingType β_A]
    [AddCommGroup β_B] [GradingType β_B] (R : Type*) [CommRing R] (ObjA ObjB : Type*)
    [AInfinityCategory β_A R ObjA] [AInfinityCategory β_B R ObjB]
    extends AInfinityFunctorData β_A β_B R ObjA ObjB where
  /-- The functor components satisfy the functor equations in every arity. -/
  satisfiesFunctorEquations :
    AInfinityFunctorData.SatisfiesFunctorEquations AInfinityCategoryStruct.m
      AInfinityCategoryStruct.m toAInfinityFunctorData

end AInfinityTheory
