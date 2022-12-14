import sheaves_of_modules.defs
/-

# Pushforward and pullback of sheaves of modules

-/

variables {X Y : RINGED_SPACE} 
namespace SHEAF_OF_MODULES

section experiment

--#check @Top.sheaf.pushforward

variable (f : X โถ Y)

example : (X : TOP) โถ Y := f.base

end experiment

--#check Top.presheaf.pushforward_obj
--set_option pp.notation false

/-
instance (๐ : SHEAF_OF_MODULES X) (U : (opens (X : TOP))แตแต) :
  module ((๐_ X) U) (๐.obj U) := ๐.module_structure U
-/

--instance (U) : module 
--#print notation _*
--#check Top.presheaf.pushforward_obj

/-

/-- Pushforward a presheaf on `X` along a continuous map `f : X โถ Y`, obtaining a presheaf
on `Y`. -/
def pushforward_obj {X Y : Top.{w}} (f : X โถ Y) (โฑ : X.presheaf C) : Y.presheaf C :=
(opens.map f).op โ โฑ

infix ` _* `: 80 := pushforward_obj
-/

--#where
def map (f : X โถ Y) (๐ : SHEAF_OF_MODULES X) : SHEAF_OF_MODULES Y :=
{ ab_sheaf := (Top.sheaf.pushforward.{0} f.base).obj ๐.ab_sheaf,
  module_structure := ฮป U, by letI : module โฅ((f.base _* X.to_PresheafedSpace.presheaf).obj U)
    โฅ(((Top.sheaf.pushforward f.base).obj ๐.ab_sheaf).val.obj U) := obj.module ๐ ((topological_space.opens.map f.base).op.obj U); exact
    module.comp_hom (๐.obj ((topological_space.opens.map f.base).op.obj U)) (f.c.app U),
--   module_structure := ฮป U, begin
-- --    delta Top.sheaf.pushforward,
-- --    dsimp only,
-- --    delta Top.presheaf.pushforward_obj,
-- --    change module _ (๐.obj _),
--     let V : (topological_space.opens (X : TOP))แตแต := (topological_space.opens.map f.base).op.obj U,
--     change module ((๐_ Y) U) (๐.obj V),
-- --    letI baz : module ((๐_ X) V) (๐.obj V) := infer_instance, -- show_term {apply_instance}
--     letI : module โฅ((f.base _* X.to_PresheafedSpace.presheaf).obj U) โฅ(๐.obj V) := obj.module ๐ V,
-- --    let foo : (๐_ Y) U โ+* (๐_ X) V := f.c.app U,
--     exact module.comp_hom (๐.obj V) (f.c.app U),
--   end,
  compatibility_bit := ฮป U V i, begin
    rintro s (n : ๐.ab_sheaf.val.obj _),
    change โฅ((๐_ Y) U) at s,
    have foo := f.c.naturality i,
    let j : ((topological_space.opens.map f.base).op.obj U) โถ ((topological_space.opens.map f.base).op.obj V) :=
      ((topological_space.opens.map f.base).op.map i),
    let r : (๐_ X) ((topological_space.opens.map f.base).op.obj U) := f.c.app U s,
    --have bar := ๐.compatibility_bit _ _ j r n,
    convert ๐.compatibility_bit _ _ j r n using 1,
    rw fun_like.ext_iff at foo,
    specialize foo s,
    have moo : (f.base _* X.to_PresheafedSpace.presheaf).map i = X.to_PresheafedSpace.presheaf.map j,
      refl,
    rw fun_like.ext_iff at moo,
    specialize moo r,
    rw โ moo,
    change _ = ((f.c.app U โซ (f.base _* X.to_PresheafedSpace.presheaf).map i) s) โข _,
    rw โ foo,
    refl,
    
    -- need to pull back i; need to fix implicits
    -- might need pen and paper here
    --convert bar _ _,
    /-
    Have foo: O_Y(U)->O_Y(V)->f_*O_X(V) = O_Y(U)->f_*O_X(U)->f_*O_X(V)
    have bar : โ r โ O_X(fโปยน(U)), m โ ๐(fโปยน(U)),
      res(rโขm) โ ๐(fโปยน(V)) = (res(r) : O_X(fโปยน(V)))โขres(m)
    
    Want: โ s โ O_Y(U), โ n โ f_*๐(U) := ๐(fโปยน(U)), res(sโขn)=res(s)โขres(n)
    Proof: define r=image of s in O_X(fโปยน(U))=f_*O_X(U). 

    -/
    --letI : module (Y.to_PresheafedSpace.presheaf.obj U) 
    --  (((Top.sheaf.pushforward f.base).obj ๐.ab_sheaf).val.obj U) := module_structure ๐ ((topological_space.opens.map f.base).op.obj U),

    --calc
    --(((Top.sheaf.pushforward f.base).obj ๐.ab_sheaf).val.map i) (s โข n) = 
    --((Y.to_PresheafedSpace.presheaf.map i) s : (๐_ Y) V) โข (((Top.sheaf.pushforward f.base).obj ๐.ab_sheaf).val.map i) n : sorry
  end }

infix (name := hi) ` _* `: 80 := map

--#check Top.sheaf.pushforward


variables (f : X โถ Y) (๐ : SHEAF_OF_MODULES X)

def map_id (๐ : SHEAF_OF_MODULES X) : (๐ X) _* ๐ โ ๐ :=
{ hom := 
  { ab_sheaf := 
    { val := 
      { app := ฮป U, ๐.ab_sheaf.val.map $ category_theory.op_hom_of_le $ ฮป x hx, hx,
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
        { app := ฮป U, ๐.ab_sheaf.val.map $ category_theory.op_hom_of_le $ ฮป x hx, hx,
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

example (Z : Type) [topological_space Z] (U V : (topological_space.opens Z)แตแต) (h : V.unop โ U.unop): 
  U โถ V :=
begin
  refine category_theory.op_hom_of_le h,
end
