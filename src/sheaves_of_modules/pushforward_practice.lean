import sheaves_of_modules.defs
/-

# Pushforward and pullback of sheaves of modules

-/

variables {X Y : RINGED_SPACE} 
namespace SHEAF_OF_MODULES

section experiment

--#check @Top.sheaf.pushforward

variable (f : X ⟶ Y)

example : (X : TOP) ⟶ Y := f.base

end experiment

--#check Top.presheaf.pushforward_obj
--set_option pp.notation false

/-
instance (𝓜 : SHEAF_OF_MODULES X) (U : (opens (X : TOP))ᵒᵖ) :
  module ((𝓞_ X) U) (𝓜.obj U) := 𝓜.module_structure U
-/

--instance (U) : module 
--#print notation _*
--#check Top.presheaf.pushforward_obj

/-

/-- Pushforward a presheaf on `X` along a continuous map `f : X ⟶ Y`, obtaining a presheaf
on `Y`. -/
def pushforward_obj {X Y : Top.{w}} (f : X ⟶ Y) (ℱ : X.presheaf C) : Y.presheaf C :=
(opens.map f).op ⋙ ℱ

infix ` _* `: 80 := pushforward_obj
-/

--#where
def map (f : X ⟶ Y) (𝓜 : SHEAF_OF_MODULES X) : SHEAF_OF_MODULES Y :=
{ ab_sheaf := (Top.sheaf.pushforward.{0} f.base).obj 𝓜.ab_sheaf,
  module_structure := λ U, by letI : module ↥((f.base _* X.to_PresheafedSpace.presheaf).obj U)
    ↥(((Top.sheaf.pushforward f.base).obj 𝓜.ab_sheaf).val.obj U) := obj.module 𝓜 ((topological_space.opens.map f.base).op.obj U); exact
    module.comp_hom (𝓜.obj ((topological_space.opens.map f.base).op.obj U)) (f.c.app U),
--   module_structure := λ U, begin
-- --    delta Top.sheaf.pushforward,
-- --    dsimp only,
-- --    delta Top.presheaf.pushforward_obj,
-- --    change module _ (𝓜.obj _),
--     let V : (topological_space.opens (X : TOP))ᵒᵖ := (topological_space.opens.map f.base).op.obj U,
--     change module ((𝓞_ Y) U) (𝓜.obj V),
-- --    letI baz : module ((𝓞_ X) V) (𝓜.obj V) := infer_instance, -- show_term {apply_instance}
--     letI : module ↥((f.base _* X.to_PresheafedSpace.presheaf).obj U) ↥(𝓜.obj V) := obj.module 𝓜 V,
-- --    let foo : (𝓞_ Y) U →+* (𝓞_ X) V := f.c.app U,
--     exact module.comp_hom (𝓜.obj V) (f.c.app U),
--   end,
  compatibility_bit := λ U V i, begin
    rintro s n,--(n : 𝓜.ab_sheaf.val.obj _),
    change ↥((𝓞_ Y) U) at s,
    have foo := f.c.naturality i,
    have baz : (X : TOP) ⟶ (Y : TOP) := f.base,
    let j : ((topological_space.opens.map f.base).op.obj U) ⟶ ((topological_space.opens.map f.base).op.obj V) :=
      ((topological_space.opens.map f.base).op.map i),
    have bar := 𝓜.compatibility_bit _ _ j, -- need to pull back i; need to fix implicits
    -- might need pen and paper here
    /-
    Have foo: O_Y(U)->O_Y(V)->f_*O_X(V) = O_Y(U)->f_*O_X(U)->f_*O_X(V)
    have bar : ∀ r ∈ O_X(f⁻¹(U)), m ∈ 𝓜(f⁻¹(U)),
      res(r•m) ∈ 𝓜(f⁻¹(V)) = (res(r) : O_X(f⁻¹(V)))•res(m)
    
    Want: ∀ s ∈ O_Y(U), ∀ n ∈ f_*𝓜(U) := 𝓜(f⁻¹(U)), res(s•n)=res(s)•res(n)
    Proof: define r=image of s in O_X(f⁻¹(U))=f_*O_X(U). 

    -/
    --letI : module (Y.to_PresheafedSpace.presheaf.obj U) 
    --  (((Top.sheaf.pushforward f.base).obj 𝓜.ab_sheaf).val.obj U) := module_structure 𝓜 ((topological_space.opens.map f.base).op.obj U),

    --calc
    --(((Top.sheaf.pushforward f.base).obj 𝓜.ab_sheaf).val.map i) (s • n) = 
    --((Y.to_PresheafedSpace.presheaf.map i) s : (𝓞_ Y) V) • (((Top.sheaf.pushforward f.base).obj 𝓜.ab_sheaf).val.map i) n : sorry
    sorry
  end }

infix (name := hi) ` _* `: 80 := map

--#check Top.sheaf.pushforward


variables (f : X ⟶ Y) (𝓜 : SHEAF_OF_MODULES X)

def map_id (𝓜 : SHEAF_OF_MODULES X) : (𝟙 X) _* 𝓜 ≅ 𝓜 :=
{ hom := 
  { ab_sheaf := 
    { val := 
      { app := λ U, 𝓜.ab_sheaf.val.map $ category_theory.op_hom_of_le $ λ x hx, hx,
        naturality' := begin
          intros U V f,
          ext,
          simp only [category_theory.comp_apply],
          sorry,
        end } },
      map_smul := begin
        intros,
        simp only [category_theory.op_hom_of_le],
        sorry,        
      end },
    inv := 
    { ab_sheaf :=
      { val := 
        { app := λ U, 𝓜.ab_sheaf.val.map $ category_theory.op_hom_of_le $ λ x hx, hx,
          naturality' := begin
            intros U V g,
            ext,
            simp only [category_theory.comp_apply],
            sorry,
          end } },
      map_smul := sorry },
  hom_inv_id' := begin
    ext U m,
    --dsimp only [category_theory.comp_apply],
    unfold_coes,
    dsimp only,
    sorry,
  end,
  inv_hom_id' := sorry }

end SHEAF_OF_MODULES

example (Z : Type) [topological_space Z] (U V : (topological_space.opens Z)ᵒᵖ) (h : V.unop ⊆ U.unop): 
  U ⟶ V :=
begin
  refine category_theory.op_hom_of_le h,
end
