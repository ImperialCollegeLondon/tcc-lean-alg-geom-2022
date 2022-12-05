import sheaves_of_modules.defs
import algebra.category.Group.colimits
/-

# ullback of sheaves of modules

-/

variables {X Y : RINGED_SPACE} 
namespace SHEAF_OF_MODULES

variables (C : Type) [category_theory.category C]

-- /-- Pullback a presheaf on `Y` along a continuous map `f : X ⟶ Y`, obtaining a presheaf
-- on `X`. -/
-- def pullback_obj {X Y : Top.{0}} (f : X ⟶ Y) (ℱ : X.presheaf C) : Y.presheaf C :=
-- sorry

--infix ` ^* `: 80 := pullback_obj
--#where

def module.mk {R M : Type*} [comm_ring R] [add_comm_group M]
  (smul : R → M →+ M) : module R M :=
{ smul := λ r m, smul r m,
  one_smul := sorry,
  mul_smul := sorry,
  smul_zero := λ r, (smul r).map_zero,
  smul_add := λ r, (smul r).map_add,
  add_smul := sorry,
  zero_smul := sorry }

noncomputable def comap (f : X ⟶ Y) (𝓜 : SHEAF_OF_MODULES Y) : SHEAF_OF_MODULES X :=
{ ab_sheaf := (category_theory.presheaf_to_Sheaf _ _).obj ((Top.presheaf.pullback Ab f.base).obj 𝓜.ab_sheaf.val),
  module_structure := λ U, 
  { smul := λ r, _,
    one_smul := _,
    mul_smul := _,
    smul_zero := _,
    smul_add := _,
    add_smul := _,
    zero_smul := _ },
  compatibility_bit := _ }

end SHEAF_OF_MODULES
