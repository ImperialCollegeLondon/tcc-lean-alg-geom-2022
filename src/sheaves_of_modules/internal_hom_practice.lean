import sheaves_of_modules.defs
/-

# Internal homs

This work is all due to Jujian Zhang.

If 𝓜 and 𝓝 are sheaves of modules on a ringed space X, then Hom(𝓜,𝓝) naturally 
has the structure of a sheaf of modules on X.

-/

/-

Given (U : topological_space.opens (X : TOP))

I want 
{U : Top} -- this is Top.of U
{f : U ⟶ (X : Top.{v})}
(h : open_embedding f)

lemma open_embedding_of_le {U V : opens α} (i : U ≤ V) :
  open_embedding (set.inclusion i) :=
{ inj := set.inclusion_injective i,
  induced := (@induced_compose _ _ _ _ (set.inclusion i) coe).symm,
  open_range :=
  begin
    rw set.range_inclusion i,
    exact U.property.preimage continuous_subtype_val
  end, }


-/

section examples

variables (X : RINGED_SPACE) (U : topological_space.opens (X : TOP)) 

#check (Top.of U : TOP)

example : Top.of U ⟶ X := _

end examples
#exit
def RINGED_SPACE.restrict (X : RINGED_SPACE) (U : topological_space.opens (X : TOP)) :
  RINGED_SPACE :=
{ carrier := _,
  presheaf := _,
  is_sheaf := _ }

namespace SHEAF_OF_MODULES

#check algebraic_geometry.SheafedSpace.restrict

def restrict (X : RINGED_SPACE) (U : topological_space.opens (X : TOP)) :
  RINGED_SPACE :=
_

variables {X : RINGED_SPACE} 

def internal_hom (𝓜 𝓝 : SHEAF_OF_MODULES X) : SHEAF_OF_MODULES X :=
{ ab_sheaf := 
  { val := 
    { obj := _,
      map := _,
      map_id' := sorry,
  map_comp' := sorry },
    cond := _ },
  module_structure := _,
  compatibility_bit := _ }


end SHEAF_OF_MODULES
