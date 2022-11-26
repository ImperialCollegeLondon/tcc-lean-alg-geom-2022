import algebraic_geometry.ringed_space
import algebra.module.basic
import tactic

/-

# Sheaves of modules

-/

-- This shoudl be elsewhere
namespace category_theory.Sheaf.hom

open category_theory

attribute [simps] category_theory.quiver.hom.has_zero

end category_theory.Sheaf.hom
/-

# Let's start by making the categories we're interested in.

-/

open algebraic_geometry topological_space


abbreviation RINGED_SPACE := RingedSpace.{0}

--#check RINGED_SPACE -- -- Type 1
-- this is a LARGE CATEGORY
-- this means: it doesn't have a set of objects
-- it has a "class" of objects
-- (topological space plus a sheaf of rings)
-- but all hom sets are sets

abbreviation TOP := Top.{0}
abbreviation AB := Ab.{0}

open category_theory

@[reducible] 
def TOP.sheaf := Top.sheaf.{0}

-- TOP and AB are also large categories

section examples

-- Let X be a topological space equipped with a sheaf of rings
variable (X : RINGED_SPACE)

-- There is a forgetful functor from the category of
-- ringed spaces to the cat of top spaces

-- #check (X : TOP) -- ↑X : TOP
-- the up-arrow means "I just applied a map which mathematicians
-- don't usually mention"

-- Let U be an open subset of X

variables (U V : (opens (X : TOP))ᵒᵖ) (i : U ⟶ V) -- V ⊆ U

-- #check X.presheaf.obj U -- `CommRing`

--notation `𝓞_ ` X := λ (U : (opens (X : TOP))ᵒᵖ), X.presheaf.obj U
notation `𝓞_ ` X := X.to_PresheafedSpace.presheaf.obj

-- Now we can use notation (𝓞_ X) for the function which eats
-- an open set and spits out a commutative ring

-- O_X(U) is a commutative ring
example : comm_ring ((𝓞_ X) U) := infer_instance 

-- the restriction homomorphism coming from the inclusion `i : V ⊆ U`
example : (𝓞_ X) U →+* (𝓞_ X) V := X.presheaf.map i

end examples

/-- Sheaf of modules for the structure sheaf of a ringed space. -/
structure SHEAF_OF_MODULES (X : RINGED_SPACE) :=
-- What is a sheaf of modules on a ringed space?
-- Firstly we'll need a sheaf of abelian groups
(ab_sheaf : TOP.sheaf AB X)
-- And secondly we need an action of the sheaf of rings
-- on the sheaf of abelian groups
(module_structure : ∀ (U : (opens (X : TOP))ᵒᵖ), 
  module ((𝓞_ X) U) (ab_sheaf.val.obj U))
-- That says "ab_sheaf(U) has the structure of a module 
-- for O_X(U) for all U"
(compatibility_bit : ∀ (U V : (opens (X : TOP))ᵒᵖ) (i : U ⟶ V)
  (r : (𝓞_ X) U) (m : ab_sheaf.val.obj U),
  (ab_sheaf.val.map i) (r • m) = (X.presheaf.map i r) • (ab_sheaf.val.map i) m)
-- This says that the module structure is compatible with all restriction morphisms
-- on O_X and on M (here called ab_sheaf).

--#check SHEAF_OF_MODULES.module_structure

-- What now?

-- We could make sheaves of modules into an abelian category
-- We could define pushforward and pullback of sheaves of modules
-- We could define tensor products of sheaves of modules
-- Everything needs doing and nobody ever did this before

/-

# Sheaves of modules are a category

-/

namespace SHEAF_OF_MODULES

variable {X : RINGED_SPACE}

def obj (𝓜 : SHEAF_OF_MODULES X) (U : (opens (X : TOP))ᵒᵖ) : AB := 𝓜.ab_sheaf.val.obj U

instance (𝓜 : SHEAF_OF_MODULES X) (U : (opens (X : TOP))ᵒᵖ) :
  module ((𝓞_ X) U) (𝓜.obj U) := 𝓜.module_structure U

@[ext]
structure hom (𝓜 𝓝 : SHEAF_OF_MODULES X) : Type := -- check it's a set!
-- morphism of underlying sheaf of abelian groups
(ab_sheaf : 𝓜.ab_sheaf ⟶ 𝓝.ab_sheaf)
(map_smul : ∀ (U : (opens (X : TOP))ᵒᵖ) (r : (𝓞_ X) U) (m : 𝓜.obj U),
  ab_sheaf.val.app U (r • m : 𝓜.obj U) = (r • (ab_sheaf.val.app U m) : 𝓝.obj U))

-- we have the objects and we have the morphisms so let's make a category!

namespace hom

-- set up the notational typeclass for hom
instance : quiver (SHEAF_OF_MODULES X) := 
{ hom := λ 𝓜 𝓝, hom 𝓜 𝓝 }

variables (𝓜 𝓝 : SHEAF_OF_MODULES X)

-- zero morphism between sheaves of modules
instance : has_zero (𝓜 ⟶ 𝓝) :=
{ zero := 
  { ab_sheaf := 0,
    map_smul := begin
      intros U r m,
      simp, -- added @[simps]
    end } }

@[reducible] def id (𝓜 : SHEAF_OF_MODULES X) : 𝓜 ⟶ 𝓜 :=
{ ab_sheaf := 𝟙 𝓜.ab_sheaf,
  map_smul := begin
    intros U r m,
    simp only [category_theory.Sheaf.category_theory.category_id_val,
 category_theory.id_apply,
 eq_self_iff_true,
 category_theory.nat_trans.id_app],
  end
   }

-- @[simp] lemma id_ab_sheaf {𝓜 : SHEAF_OF_MODULES X} : 
--   (hom.id 𝓜 : 𝓜 ⟶ 𝓜).ab_sheaf = 𝟙 (𝓜.ab_sheaf) := rfl

@[reducible] def comp {𝓜 𝓝 𝓟 : SHEAF_OF_MODULES X}
  (φ : 𝓜 ⟶ 𝓝) (ψ : 𝓝 ⟶ 𝓟) : 𝓜 ⟶ 𝓟 :=
{ ab_sheaf := φ.ab_sheaf ≫ ψ.ab_sheaf,
  map_smul := begin
    intros,
    simp [φ.map_smul, ψ.map_smul],
  end }

-- don't need because comp reducible
-- @[simp] lemma comp_ab_sheaf {𝓜 𝓝 𝓟 : SHEAF_OF_MODULES X}
--   (φ : 𝓜 ⟶ 𝓝) (ψ : 𝓝 ⟶ 𝓟) : (comp φ ψ).ab_sheaf = φ.ab_sheaf ≫ ψ.ab_sheaf := rfl

end hom

instance : large_category (SHEAF_OF_MODULES X) :=
{ hom := hom,
  id := hom.id,
  comp := λ 𝓜 𝓝 𝓟, hom.comp,
  id_comp' := begin
    intros 𝓜 𝓝 φ,
    ext U m,
    simp only [category.id_comp],
  end,
  comp_id' := begin
    intros,
    ext,
    simp only [category.comp_id],
  end,
  assoc' := begin
    intros,
    ext,
    simp only [category.assoc],
  end }

-- #check 𝓜 ⟶ 𝓝

end SHEAF_OF_MODULES

/-

Possible future work: sheaves are an abelian category,
pushforward and pullback of sheaves of modules, 
tensor product of sheaves of modules.
Construction of a sheaf of modules on Spec(R)
from a module over a ring
-/