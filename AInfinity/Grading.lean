/-
Copyright (c) 2026 Justin Mu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justin Mu, Annie Yao, Niels Voss, Marco David
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.GradedObject

/-! # Graded modules and quivers for A-infinity categories

This file introduces graded hom spaces and `R`-linear graded quivers. The grading
type is kept unconstrained here; the algebraic structure needed for degrees and
Koszul signs is imposed by the A-infinity structures that use these definitions.
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

end AInfinityTheory
