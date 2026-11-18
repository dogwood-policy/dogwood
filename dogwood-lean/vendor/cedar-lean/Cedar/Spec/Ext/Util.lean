module

namespace Cedar.Spec.Ext

----- Helper Functions -----

/--
Helper function that wraps String.toInt? but returns .none if the string contains '_'.
This prevents the undocumented behavior where String.toInt? allows '_' characters.
-/
public def toInt?' (str : String) : Option Int :=
  if str.contains '_' then .none else String.toInt? str

/--
Helper function that wraps String.toNat? but returns .none if the string contains '_'.
This prevents the undocumented behavior where String.toNat? allows '_' characters.
-/
public def toNat?' (str : String) : Option Nat :=
  if str.contains '_' then .none else String.toNat? str
