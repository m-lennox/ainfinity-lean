/-
Copyright (c) 2026 Justin Mu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justin Mu, Annie Yao, Niels Voss, Marco David
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.GradedObject
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.ZMod.IntUnitsPower

/-! # Gradings for A-infinity categories

This file introduces graded hom spaces, `R`-linear graded quivers, and the grading data
needed to write down A-infinity structures.

The grading type `β` of an A-infinity category is an abelian group of degrees. The
A-infinity axioms only ever use two pieces of additional structure on it:

* integer *degree shifts* `ℤ →+ β`, so that the `n`-ary operation `mₙ` can have degree
  `2 - n`;
* a *Koszul sign character* `β →+ Additive ℤˣ`, so that a degree `d` determines a sign
  `(-1) ^ d`.

They are compatible in that the differential, of degree `shift 1`, is odd.

No degree is ever multiplied, so `β` is *not* required to be a ring. This is what allows
bigradings such as `ℤ × ℤ` or `ℤ × ZMod 2`, where `mₙ` has degree `(2 - n, 0)` and the
sign is the total parity.
-/

namespace AInfinityTheory

universe u v w

variable (β : Type v)

/-- A graded `R`-module indexed by `β`. -/
public abbrev GradedRModule (R : Type u) [CommRing R] :=
  CategoryTheory.GradedObject β (ModuleCat.{u} R)

/-- An `R`-linear graded quiver. -/
public class RLinearGradedQuiver (R : Type u) [CommRing R] (Obj : Type w) where
  /-- The graded `R`-module of morphisms from `X` to `Y`. -/
  protected gradedHom' : Obj → Obj → GradedRModule β R

/-- The graded `R`-module of morphisms between two objects. -/
@[expose]
public def gradedHom (R : Type u) [CommRing R]
    {Obj : Type w} [RLinearGradedQuiver β R Obj] (X Y : Obj) : GradedRModule β R :=
  RLinearGradedQuiver.gradedHom' X Y

/-- A grading index is an abelian group of degrees `β` together with a homomorphism
`shift : ℤ →+ β` realising integer degree shifts (the `n`-ary operation `mₙ` has degree
`shift (2 - n)`) and a Koszul sign character `sign : β →+ Additive ℤˣ`, such that the
differential, of degree `shift 1`, is odd. -/
public class GradingIndex (β : Type*) [AddCommGroup β] where
  /-- The integer degree shifts: `mₙ` has degree `shift (2 - n)`. -/
  shift : ℤ →+ β
  /-- The Koszul sign character, written additively. -/
  sign : β →+ Additive ℤˣ
  /-- The differential has odd degree. -/
  sign_shift_one : sign (shift 1) = Additive.ofMul (-1)

export GradingIndex (shift)

variable {β}

section GradingIndex

variable [AddCommGroup β] [GradingIndex β]

/-- The Koszul sign `(-1) ^ d ∈ ℤˣ` attached to a degree `d : β`. -/
@[expose]
public def negOnePow (d : β) : ℤˣ :=
  Additive.toMul (GradingIndex.sign d)

@[simp]
public lemma negOnePow_zero : negOnePow (0 : β) = 1 := by
  simp only [negOnePow, map_zero, toMul_zero]

@[simp]
public lemma negOnePow_add (a b : β) : negOnePow (a + b) = negOnePow a * negOnePow b := by
  simp only [negOnePow, map_add, toMul_add]

@[simp]
public lemma negOnePow_neg (a : β) : negOnePow (-a) = negOnePow a := by
  simp only [negOnePow, map_neg, toMul_neg, Int.units_inv_eq_self]

@[simp]
public lemma negOnePow_sub (a b : β) : negOnePow (a - b) = negOnePow a * negOnePow b := by
  rw [sub_eq_add_neg, negOnePow_add, negOnePow_neg]

@[simp]
public lemma negOnePow_sum {ι : Type*} (s : Finset ι) (f : ι → β) :
    negOnePow (∑ i ∈ s, f i) = ∏ i ∈ s, negOnePow (f i) := by
  simp only [negOnePow, map_sum, toMul_sum]

/-- An integer degree shift is written `n • shift 1`. -/
public lemma shift_eq_zsmul_shift_one (n : ℤ) : (shift n : β) = n • shift (1 : ℤ) := by
  rw [← map_zsmul, smul_eq_mul, mul_one]

/-- The sign of an integer degree shift is Mathlib's `Int.negOnePow`. -/
@[simp]
public lemma negOnePow_shift (n : ℤ) : negOnePow (shift n : β) = Int.negOnePow n := by
  rw [negOnePow, shift_eq_zsmul_shift_one, map_zsmul, GradingIndex.sign_shift_one,
    ← ofMul_zpow, toMul_ofMul, Int.negOnePow_def]
  rfl

/-- The differential is odd. -/
public lemma negOnePow_shift_one : negOnePow (shift (1 : ℤ) : β) = -1 := by
  rw [negOnePow_shift, Int.negOnePow_one]

end GradingIndex

namespace GradingIndex

/-! ### Instances

Global instances are provided only for the two standard gradings `ℤ` and `ZMod 2`. Product
gradings are constructed by the named definitions `prodFst` and `prodTotal` below and must be
activated locally, since both are reasonable choices on the same product type. -/

/-- The integers, graded by themselves: the shift is the identity and the sign of `n` is
`(-1) ^ n`. -/
public instance int : GradingIndex ℤ where
  shift := AddMonoidHom.id ℤ
  sign := zmultiplesHom (Additive ℤˣ) (Additive.ofMul (-1))
  sign_shift_one := by
    simp only [AddMonoidHom.id_apply, zmultiplesHom_apply, one_zsmul]

@[simp]
public lemma shift_int (n : ℤ) : shift n = n := rfl

/-- The parity grading `ZMod 2`: the shift is reduction modulo `2` and the sign of a parity
`p` is `(-1) ^ p`, using Mathlib's power operation on `ℤˣ` by `ZMod 2`. -/
public instance zmodTwo : GradingIndex (ZMod 2) where
  shift := Int.castAddHom (ZMod 2)
  sign := (smulAddHom (ZMod 2) (Additive ℤˣ)).flip (Additive.ofMul (-1))
  sign_shift_one := by
    simp only [Int.coe_castAddHom, Int.cast_one, AddMonoidHom.flip_apply, smulAddHom_apply,
      one_smul]

@[simp]
public lemma shift_zmod_two (n : ℤ) : shift n = (n : ZMod 2) := rfl

section Prod

variable (β : Type*) [AddCommGroup β] (γ : Type*) [AddCommGroup γ]

/-- The product grading on `β × γ` whose shifts land in the first factor and whose sign is
read off the first factor alone. -/
public abbrev prodFst [GradingIndex β] : GradingIndex (β × γ) where
  shift := (AddMonoidHom.inl β γ).comp shift
  sign := sign.comp (AddMonoidHom.fst β γ)
  sign_shift_one := by
    simp only [AddMonoidHom.coe_comp, AddMonoidHom.coe_fst, Function.comp_apply,
      AddMonoidHom.inl_apply, sign_shift_one]

@[simp]
public lemma prodFst_shift [GradingIndex β] (n : ℤ) :
    (prodFst β γ).shift n = (shift n, 0) := rfl

/-- The product grading on `β × γ` whose shifts land in the first factor and whose sign is
the product of the signs of both factors (the *total* sign). -/
public abbrev prodTotal [GradingIndex β] [GradingIndex γ] : GradingIndex (β × γ) where
  shift := (AddMonoidHom.inl β γ).comp shift
  sign := AddMonoidHom.coprod sign sign
  sign_shift_one := by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.inl_apply,
      AddMonoidHom.coprod_apply, sign_shift_one, map_zero, add_zero]

@[simp]
public lemma prodTotal_shift [GradingIndex β] [GradingIndex γ] (n : ℤ) :
    (prodTotal β γ).shift n = (shift n, 0) := rfl

end Prod

end GradingIndex

/-! ### Koszul signs in the standard gradings -/

@[simp]
public lemma negOnePow_int (n : ℤ) : negOnePow n = Int.negOnePow n := rfl

/-- In the parity grading, `negOnePow` is Mathlib's power operation on `ℤˣ` by `ZMod 2`. -/
public lemma negOnePow_zmod_two (p : ZMod 2) : negOnePow p = (-1 : ℤˣ) ^ p := rfl

@[simp]
public lemma negOnePow_intCast_zmod_two (n : ℤ) : negOnePow (n : ZMod 2) = Int.negOnePow n :=
  negOnePow_shift n

section Prod

variable (β : Type*) [AddCommGroup β] (γ : Type*) [AddCommGroup γ]

@[simp]
public lemma negOnePow_prodFst [GradingIndex β] (d : β × γ) :
    @negOnePow (β × γ) _ (GradingIndex.prodFst β γ) d = negOnePow d.1 := rfl

@[simp]
public lemma negOnePow_prodTotal [GradingIndex β] [GradingIndex γ] (d : β × γ) :
    @negOnePow (β × γ) _ (GradingIndex.prodTotal β γ) d = negOnePow d.1 * negOnePow d.2 := rfl

end Prod

end AInfinityTheory
