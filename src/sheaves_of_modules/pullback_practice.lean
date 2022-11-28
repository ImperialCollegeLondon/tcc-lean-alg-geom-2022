import sheaves_of_modules.defs
/-

# ullback of sheaves of modules

-/

variables {X Y : RINGED_SPACE} 
namespace SHEAF_OF_MODULES

variables (C : Type) [category_theory.category C]

/-- Pullback a presheaf on `Y` along a continuous map `f : X ⟶ Y`, obtaining a presheaf
on `X`. -/
def pullback_obj {X Y : Top.{0}} (f : X ⟶ Y) (ℱ : X.presheaf C) : Y.presheaf C :=
sorry

infix ` ^* `: 80 := pullback_obj

--#where
def comap (f : X ⟶ Y) (𝓜 : SHEAF_OF_MODULES Y) : SHEAF_OF_MODULES X :=
sorry

end SHEAF_OF_MODULES
