module

public import Mathlib

@[expose] public section

open ChainComplex CategoryTheory DirectSum GradedMonoid GradedObject

namespace AInfinityTheory

universe u v w

variable (β : Type v)

abbrev GradedRModule (R : Type u) [CommRing R] :=
  GradedObject β (ModuleCat.{u} R)

/-- The graded R-module of morphisms between two objects. -/
class RLinearGQuiver (R : Type u) [CommRing R] (Obj : Type w) where
  protected GHom' : Obj → Obj → GradedRModule β R

def GHom (R : Type u) [CommRing R] {Obj : Type w} [RLinearGQuiver β R Obj] (X Y : Obj) : GradedRModule β R :=
  RLinearGQuiver.GHom' X Y

end AInfinityTheory
