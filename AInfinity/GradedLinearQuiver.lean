/-
Copyright (c) 2026 Annie Yao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Annie Yao, Marco David, Zhan Shi
-/
module

public import Mathlib.Algebra.Module.Equiv.Defs

/-! # Graded linear quivers

A graded `R`-linear quiver on a type of objects `Obj` assigns to each pair of objects `X Y`
and each degree `i : β` an `R`-module `Hom X Y i` of morphisms of degree `i`. It is the
underlying data of an `A∞`-category, before any compositions are chosen.

## Main definitions

* `AInfinityTheory.GradedLinearQuiver β R Obj`: a graded `R`-linear quiver.
* `AInfinityTheory.GradedLinearQuiver.ComposableHomType`: the hom space containing the `i`-th
  morphism of a composable string of objects.
* `AInfinityTheory.GradedLinearQuiver.homCongr`: transport between graded hom spaces along
  equalities of the source, target and degree.
-/

@[expose] public section

namespace AInfinityTheory

universe u v w w'

section

variable (β : Type v) (R : outParam (Type u)) [CommRing R] (Obj : Type w)

/-- A graded `R`-linear quiver: for objects `X Y` and a degree `i`, the morphisms of degree `i`
from `X` to `Y` form an `R`-module `Hom X Y i`. -/
class GradedLinearQuiver where
  /-- The morphisms of degree `i` from `X` to `Y`. -/
  Hom : Obj → Obj → β → Type w'
  /-- Each graded piece of a hom space is an abelian group. -/
  homGroup : ∀ X Y i, AddCommGroup (Hom X Y i) := by infer_instance
  /-- Each graded piece of a hom space is an `R`-module. -/
  homModule : ∀ X Y i, Module R (Hom X Y i) := by infer_instance

attribute [instance_reducible, instance] GradedLinearQuiver.homGroup
  GradedLinearQuiver.homModule

end

namespace GradedLinearQuiver

variable {β : Type v} {R : Type u} [CommRing R] {Obj : Type w} [GradedLinearQuiver β R Obj]
variable {n : ℕ}

/-- The hom space containing the `i`-th morphism of a composable string of objects, in
degree `b`. -/
abbrev ComposableHomType (obj : Fin (n + 1) → Obj) (i : Fin n) (b : β) : Type w' :=
  Hom (obj i.castSucc) (obj i.succ) b

/-- Transport between graded hom spaces along equalities of the source, target and degree.
This is the three-index form of `LinearEquiv.cast`. -/
def homCongr
    {X X' Y Y' : Obj}
    {i i' : β}
    (hX : X = X')
    (hY : Y = Y')
    (hi : i = i') :
    Hom X Y i ≃ₗ[R] Hom X' Y' i' := by
  subst hX hY hi
  exact LinearEquiv.refl R _

/-- Transport along reflexivity is the identity. -/
@[simp]
lemma homCongr_refl
    (X Y : Obj)
    (i : β) :
    homCongr (rfl : X = X) (rfl : Y = Y) (rfl : i = i) = LinearEquiv.refl R _ :=
  rfl

/-- The inverse of a transport is the transport along the reversed equalities. -/
@[simp]
lemma homCongr_symm
    {X X' Y Y' : Obj}
    {i i' : β}
    (hX : X = X')
    (hY : Y = Y')
    (hi : i = i') :
    (homCongr hX hY hi).symm = homCongr hX.symm hY.symm hi.symm := by
  subst hX hY hi
  rfl

/-- Transporting twice is transporting along the composite equalities. -/
@[simp]
lemma homCongr_trans
    {X X' X'' Y Y' Y'' : Obj}
    {i i' i'' : β}
    (hX : X = X')
    (hY : Y = Y')
    (hi : i = i')
    (hX' : X' = X'')
    (hY' : Y' = Y'')
    (hi' : i' = i'') :
    (homCongr hX hY hi).trans (homCongr hX' hY' hi') =
      homCongr (hX.trans hX') (hY.trans hY') (hi.trans hi') := by
  subst hX hY hi hX' hY' hi'
  rfl

end GradedLinearQuiver

end AInfinityTheory
