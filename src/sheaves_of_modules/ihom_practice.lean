import algebra.category.Group.limits
import category_theory.preadditive.functor_category
import topology.sheaves.sheaf
import topology.sheaves.sheaf_condition.unique_gluing

import sheaves_of_modules.defs

noncomputable theory

open category_theory category_theory.limits

namespace Top.presheaf

section

universe u

variables {X : Top.{u}}

open topological_space Top opposite

/--
The inclusion `U ⟶ X`
-/
@[simps] def emb (U : opens X) : Top.of U ⟶ X :=
{ to_fun := (coe : U → X),
  continuous_to_fun := continuous_subtype_val }

/--
If `U` is open, then any open subset `V` is also an open subset of `X`.
-/
def emb.to_global_subset {U : opens X} (V : opens (Top.of U)) : opens X :=
⟨subtype.val '' V.1, (is_open.open_embedding_subtype_coe U.2).is_open_map _ V.2⟩

/--
If `U ⊆ V` are open sets in `X` and `W ⊆ U` is open in `U` then `W` is open in `V`.
-/
def emb.of_subset {U V : opens X} (inc : U ⟶ V) (W : opens (Top.of U)) : opens (Top.of V) :=
{ val := (λ p, ⟨p.1, le_of_hom inc p.2⟩ : U → V) '' W.1,
  property := let ⟨O, hO1, hO2⟩ := is_open_induced_iff.mp W.2 in
    is_open_induced_iff.mpr ⟨subtype.val '' W.1,
    begin
      apply_fun set.image subtype.val at hO2,
      rw ←hO2,
      apply (is_open.open_embedding_subtype_coe U.2).is_open_map,
      apply is_open.preimage,
      continuity,
    end, begin
      ext ⟨x, hx⟩, split,
      { rintros ⟨p, hp1, hp2⟩,
        rw set.mem_image,
        refine ⟨p, hp1, subtype.ext_iff_val.mpr hp2⟩, },
      { rintros ⟨p, hp1, hp2⟩,
        rw [←hp2, set.mem_preimage, set.mem_image],
        refine ⟨p, hp1, rfl⟩, },
    end⟩ }

/--
If `U ⊆ V` are open sets in `X` and `W₁ ⊆ W₂ ⊆ U` is open in `U` then 
`W₁ ⊆ W₂` is open in `V`.
-/
def emb.of_subset_hom {U V : opens X} (inc : U ⟶ V) 
  {W₁ W₂ : opens (Top.of U)} (i : W₁ ⟶ W₂) :
  emb.of_subset inc W₁ ⟶ emb.of_subset inc W₂ :=
hom_of_le $ λ _ ⟨q, hq1, hq2⟩, ⟨q, le_of_hom i hq1, hq2⟩

lemma emb.of_subset_id (U : opens X) (W : opens (Top.of U)) :
  emb.of_subset (𝟙 U) W = W :=
begin
  ext x, split,
  { rintros ⟨p, hp, rfl⟩, dsimp, erw opens.mem_coe at hp, convert hp, ext, refl, },
  { intros h, rw opens.mem_coe at h, refine ⟨x, h, _⟩, ext, refl, },
end

lemma emb.of_subset_comp 
  {U V W : opens X} (iUV : U ⟶ V) (iVW : V ⟶ W) (W : opens (Top.of U)) :
  emb.of_subset (iUV ≫ iVW) W = emb.of_subset iVW (emb.of_subset iUV W) :=
begin
  ext x, split,
  { rintros ⟨p, hp, rfl⟩, exact ⟨⟨p, le_of_hom iUV p.2⟩, ⟨p, hp, rfl⟩, rfl⟩, },
  { rintros ⟨p, ⟨q, hq, rfl⟩, rfl⟩, exact ⟨q, hq, rfl⟩, },
end

lemma emb.open_embedding (U : opens X) : open_embedding (emb U) :=
is_open.open_embedding_subtype_coe U.2

/--
Let `F` is a presheaf of abelian groups on `X` and `U ⊆ X` is open, this is
`F |_ V`, i.e. `(F |_ V)(W) = F(W)`
-/
@[simps] def restrict' (F : presheaf AddCommGroup.{u} X) (U : opens X) : 
  presheaf AddCommGroup (Top.of U) :=
(emb.open_embedding U).is_open_map.functor.op ⋙ F

localized "infix `|_`:40 := Top.presheaf.restrict'" in sheaf

/--
any presheaf morphism `F |_ U ⟶ G |_ U` gives a group morphism `F(U) ⟶ G(U)`
by taking gloabal sections.
-/
@[simps] def sections_map_from_restrict' {F G : presheaf AddCommGroup.{u} X} {U : opens X}
  (α : F |_ U ⟶  G |_ U) : 
  F.obj (op U) ⟶ G.obj (op U) :=
F.map (hom_of_le $ by { rintros _ ⟨x, hx, rfl⟩, exact x.2 } :
  (emb.open_embedding U).is_open_map.functor.obj ⊤ ⟶ U).op ≫ α.app (op ⊤) ≫
  G.map (hom_of_le $ λ x hx, ⟨⟨x, hx⟩, ⟨⟩, rfl⟩ :
    U ⟶ (emb.open_embedding U).is_open_map.functor.obj ⊤).op

/--
restriction is functorial.
-/
@[simps] def restrict_functor (U : opens X) : 
  presheaf AddCommGroup.{u} X ⥤ presheaf AddCommGroup (Top.of U) :=
{ obj := λ F, F |_ U,
  map := λ F G α,
  { app := λ V, α.app _,
    naturality' := λ V W inc,
    begin
      ext x,
      erw [restrict'_map, α.naturality, restrict'_map, comp_apply],
    end },
  map_id' := λ F,
  begin
    ext U x,
    simp only [nat_trans.id_app, id_apply],
  end,
  map_comp' := λ F G H α β,
  begin
    ext U x,
    simp only [nat_trans.comp_app],
  end }

/--
Some glue: if `W ⊆ U ⊆ V` are open sets of `X`, then
`(F |_ U)(W) ≅ (F |_ V)(W)`
-/
@[reducible] def restrict_subset_sections 
  (F : presheaf AddCommGroup.{u} X) {U V : opens X} (inc : U ⟶ V)
  (W : opens (Top.of U)) :
  (F |_ U).obj (op W) ≅ (F |_ V).obj (op $ emb.of_subset inc W) :=
{ hom := F.map (quiver.hom.op $ hom_of_le
    begin
      rintros p ⟨⟨q, hq1⟩, ⟨x, hx1, hx2⟩, rfl⟩,
      dsimp only at hx2,
      refine ⟨x, hx1, _⟩,
      rw ←hx2,
      refl,
    end : op ((emb.open_embedding U).is_open_map.functor.obj W) ⟶
      op ((emb.open_embedding V).is_open_map.functor.obj (emb.of_subset inc W))),
  inv := F.map (quiver.hom.op $ hom_of_le
    begin
      rintros p ⟨q, hq, rfl⟩,
      refine ⟨⟨q.1, le_of_hom inc q.2⟩, ⟨q, hq, rfl⟩, rfl⟩,
    end : op ((emb.open_embedding V).is_open_map.functor.obj (emb.of_subset inc W)) ⟶
      op ((emb.open_embedding U).is_open_map.functor.obj W)),
  hom_inv_id' := by { rw [←F.map_comp, ←op_comp], convert F.map_id _ },
  inv_hom_id' := by { rw [←F.map_comp, ←op_comp], convert F.map_id _ } }

/--
Auxiliary for:
If `U ⊆ V` are open sets, then any presheaf morphism `F |_ V ⟶ G |_ V` induces
a morphism `F |_ U ⟶ F |_ V`
-/
@[simps] def restrict_subset_sections_map.app {F G : presheaf AddCommGroup.{u} X}
  {U V : opens X} (inc : U ⟶ V)
  (α : F |_ V ⟶ G |_ V) (W : opens (Top.of U)):
  (F |_ U).obj (op W) ⟶ (G |_ U).obj (op W) :=
{ to_fun := λ s, (restrict_subset_sections G inc W).inv $ α.app _ $
      (restrict_subset_sections F inc W).hom s,
  map_zero' := by rw [map_zero, map_zero, map_zero],
  map_add' := λ x y, by rw [map_add, map_add, map_add] }

/--
Auxiliary for:
If `U ⊆ V` are open sets, then any presheaf morphism `F |_ V ⟶ G |_ V` induces
a morphism `F |_ U ⟶ F |_ V`
-/
lemma restrict_subset_sections_map.naturality {F G : presheaf AddCommGroup.{u} X}
  {U V : opens X} (inc : U ⟶ V)
  (α : restrict' F V ⟶ restrict' G V)
  (W₁ W₂ : (opens (Top.of U)))
  (i : W₁ ⟶ W₂) :
  (restrict' F U).map i.op ≫ restrict_subset_sections_map.app inc α W₁ =
    restrict_subset_sections_map.app inc α W₂ ≫ (restrict' G U).map i.op :=
begin
  ext x,
  simp only [restrict'_map, quiver.hom.unop_op, restrict_subset_sections_map.app, comp_apply,
    add_monoid_hom.coe_mk],
  simp only [←comp_apply],
  simp only [←comp_apply, ←F.map_comp, ←op_comp],
  generalize_proofs h1 h2 h3 h4 h5 h6,
  rw [show hom_of_le h3 ≫ h1.functor.map i = h2.functor.map (emb.of_subset_hom inc i) ≫
    hom_of_le h5, from rfl, op_comp, F.map_comp, category.assoc _ _ (α.app _)],
  have := α.naturality (emb.of_subset_hom inc i).op,
  dsimp at this,
  erw this,
  simp only [category.assoc],
  congr' 3,
  rw [←G.map_comp, ←G.map_comp, ←op_comp, ←op_comp],
  congr' 1,
end

/--
If `U ⊆ V` are open sets, then any presheaf morphism `F |_ V ⟶ G |_ V` induces
a morphism `F |_ U ⟶ F |_ V`
-/
@[simps] def restrict_subset_sections_map {F G : presheaf AddCommGroup.{u} X}
  {U V : opens X} (inc : U ⟶ V)
  (α : F |_ V ⟶ G |_ V) :
  F |_ U ⟶ G |_ U :=
{ app := λ W, restrict_subset_sections_map.app inc α W.unop,
  naturality' := λ W₁ W₂ i, restrict_subset_sections_map.naturality inc α _ _ i.unop }

/--
The morphsisms between restricted presheaves form an abelian group.
-/
instance (F G : presheaf AddCommGroup.{u} X) (U : opens X) :
  add_comm_group (F |_ U ⟶ G |_ U) :=
begin
  haveI i1 : preadditive (presheaf AddCommGroup (Top.of U)) :=
    category_theory.functor_category_preadditive,
  exactI i1.1 (restrict' F U) (restrict' G U),
end

@[simp] lemma sections_map_from_restrict'_zero {F G : presheaf AddCommGroup.{u} X} {U : opens X} :
  sections_map_from_restrict' (0 : F |_ U ⟶ G |_ U) = 0 :=
by ext; simp

lemma sections_map_from_restrict'_add {F G : presheaf AddCommGroup.{u} X} {U : opens X}
  (α β : F |_ U ⟶ G |_ U) :
  sections_map_from_restrict' (α + β) = 
  sections_map_from_restrict' α + 
  sections_map_from_restrict' β :=
by ext; simp

/--
The group homomorphism from `Hom_{Psh}(F |_ U, G |_ U)` to `Hom_{Ab}(F U, G U)`
-/
@[simps] def sections_map_from_restrict'_add_monoid_hom (F G : presheaf AddCommGroup.{u} X) (U : opens X) :
  AddCommGroup.of (F |_ U ⟶ G |_ U) ⟶ 
  AddCommGroup.of (F.obj (op U) ⟶ G.obj (op U)) :=
{ to_fun := sections_map_from_restrict',
  map_zero' := sections_map_from_restrict'_zero,
  map_add' := sections_map_from_restrict'_add }

lemma restrict_subset_sections_map_zero {F G : presheaf AddCommGroup.{u} X}
  {U V : opens X} (inc : U ⟶ V) :
  restrict_subset_sections_map inc (0 : restrict' F V ⟶ restrict' G V) = 0 :=
by { ext, simp }

lemma restrict_subset_sections_map_add {F G : presheaf AddCommGroup.{u} X}
  {U V : opens X} (inc : U ⟶ V) (α β : restrict' F V ⟶ restrict' G V) :
  restrict_subset_sections_map inc (α + β) = restrict_subset_sections_map inc α +
  restrict_subset_sections_map inc β :=
by { ext, simp }

lemma restrict_subset_sections_map_id {F G : presheaf AddCommGroup.{u} X} (U : opens X)
  (α : F |_ U ⟶ G |_ U) : 
  restrict_subset_sections_map (𝟙 U) α = α :=
begin
  ext W x,
  simp only [restrict_subset_sections_map_app, restrict_subset_sections_map.app_apply],
  erw [←comp_apply, ←comp_apply, ←α.naturality],
  swap,
  { refine eq_to_hom _,
    rw emb.of_subset_id U W.unop,
    refl, },
  dsimp,
  rw [←category.assoc, ←F.map_comp, ←op_comp],
  congr' 1,
  convert category.id_comp _,
  convert F.map_id _,
end

lemma restrict_subset_sections_map_comp {F G : presheaf AddCommGroup.{u} X} {U V W : opens X}
  (iUV : U ⟶ V) (iVW : V ⟶ W) 
  (α : F |_ W ⟶ G |_ W) :
  restrict_subset_sections_map (iUV ≫ iVW) α =
  restrict_subset_sections_map iUV (restrict_subset_sections_map iVW α) :=
begin
  ext O x,
  simp only [restrict_subset_sections_map_app, restrict_subset_sections_map.app_apply],
  simp only [←comp_apply, category.assoc, ←G.map_comp, ←op_comp],
  rw [←category.assoc _ _ (α.app _ ≫ _), ←F.map_comp, ←op_comp],
  congr' 1,
  change _ = _ ≫ α.app (op (emb.of_subset iVW (emb.of_subset iUV _))) ≫ _,
  generalize_proofs h1 h2 h3 h4 h5 h6 h7 h8 h9,
  rw [show α.app (op (emb.of_subset iVW (emb.of_subset iUV O.unop))) =
    F.map ((emb.open_embedding W).is_open_map.functor.op.map (eq_to_hom _)) ≫
      α.app (op (emb.of_subset (iUV ≫ iVW) O.unop)) ≫
      G.map ((emb.open_embedding W).is_open_map.functor.op.map (eq_to_hom _)),
    from _, category.assoc, category.assoc, ←G.map_comp, ←category.assoc (F.map _) (F.map _),
    ←F.map_comp],
  congr' 1,
  { rw emb.of_subset_comp, },
  { rw emb.of_subset_comp, },
  { erw [←category.assoc, α.naturality, category.assoc, ←G.map_comp],
    symmetry,
    convert category.comp_id _,
    convert G.map_id _, },
end

namespace monoidal

/--
The internal hom between `F, G` is defined to be:

* obj level: `U ↦ Hom_{Psh}(F |_ U, G |_ U)`
* map level: if `U ⊆ V` and `α : F |_ V ⟶ F |_U`, use `restrict_subset_sections_map`.
-/
@[simps] def ihom_obj (F G : presheaf AddCommGroup.{u} X) : presheaf AddCommGroup.{u} X :=
{ obj := λ U, AddCommGroup.of (F |_ U.unop ⟶ G |_ U.unop),
  map := λ U V inc,
  { to_fun := λ α, restrict_subset_sections_map inc.unop α,
    map_zero' := restrict_subset_sections_map_zero inc.unop,
    map_add' := λ α β, restrict_subset_sections_map_add inc.unop α β },
  map_id' := λ U,
  begin
    ext1,
    rw [add_monoid_hom.coe_mk, unop_id, restrict_subset_sections_map_id, id_apply],
  end,
  map_comp' := λ U V W iUV iVW,
  begin
    ext1 α,
    rw [add_monoid_hom.coe_mk, comp_apply, add_monoid_hom.coe_mk, add_monoid_hom.coe_mk],
    convert restrict_subset_sections_map_comp iVW.unop iUV.unop α,
  end }
-- 𝓗𝓸𝓶
-- ℋℴ𝓂
localized "notation `⟦` F, G`⟧` := Top.presheaf.monoidal.ihom_obj F G" in sheaf

/--
If `F, G₁, G₂` are presheaves and `γ : G₁ ⟶ G₂` and `f : F |_ U ⟶ G₁ |_ U`:
`γ` gives a map `G₁ |_ U ⟶ G₂ |_ U`, composing it with `f` to get `F |_ U ⟶ G₂ |_ U`
-/
@[simps] def ihom_map' (F G₁ G₂ : presheaf AddCommGroup.{u} X) (γ : G₁ ⟶ G₂)
  (U : opens X) (f : F |_ U ⟶ G₁ |_ U) :
  F |_ U ⟶ G₂ |_ U :=
f ≫ (restrict_functor U).map γ

lemma ihom_map'_zero (F G₁ G₂ : presheaf AddCommGroup.{u} X) (γ : G₁ ⟶ G₂) (U : opens X) :
  ihom_map' F G₁ G₂ γ U 0 = 0 :=
by ext; simp

lemma ihom_map'_add (F G₁ G₂ : presheaf AddCommGroup.{u} X) (γ : G₁ ⟶ G₂) (U : opens X)
  (α β : restrict' F U ⟶ restrict' G₁ U) :
  ihom_map' F G₁ G₂ γ U (α + β) = ihom_map' F G₁ G₂ γ U α + ihom_map' F _ _ γ U β :=
by ext; simp

lemma ihom_map'_naturality (F G₁ G₂ : presheaf AddCommGroup.{u} X)
  (γ : G₁ ⟶ G₂) (U : opens X) (α : F |_ U ⟶ G₁ |_ U)
  {W₁ W₂ : opens (Top.of U)} (inc : W₁ ⟶ W₂) :
  (F |_ U).map inc.op ≫ (ihom_map' F G₁ G₂ γ U α).app (op W₁) =
  (ihom_map' F G₁ G₂ γ U α).app (op W₂) ≫ (G₂ |_ U).map inc.op :=
begin
  ext x,
  simp only [restrict'_map, quiver.hom.unop_op, comp_apply, ihom_map'_app_apply],
  simp only [←comp_apply, category.assoc, ←G₂.map_comp],
  erw [←γ.naturality,
    ←category.assoc (α.app _), ←α.naturality],
  congr,
  exact inc.op,
end

/--
internal presheaf hom is functorial
-/
@[simps] def ihom_map_app (F G₁ G₂ : presheaf AddCommGroup.{u} X) (γ : G₁ ⟶ G₂) (U : opens X) :
  ⟦F, G₁⟧.obj (op U) ⟶ ⟦F, G₂⟧.obj (op U) :=
{ to_fun := λ α,
  { app := λ W, (ihom_map' F G₁ G₂ γ U α).app W,
    naturality' := λ W₁ W₂ inc,
    by convert ihom_map'_naturality F G₁ G₂ γ U α inc.unop },
  map_zero' :=
  begin
    ext W x,
    simp_rw ihom_map'_zero F G₁ G₂ γ U,
  end,
  map_add' := λ _ _,
  begin
    ext W x,
    simp_rw ihom_map'_add F G₁ G₂ γ U,
    rw [nat_trans.app_add, nat_trans.app_add],
  end }

/--
internal presheaf hom is functorial
-/
lemma ihom_map_naturality (F G₁ G₂ : presheaf AddCommGroup.{u} X) (γ : G₁ ⟶ G₂)
  {U V : opens X} (iUV : U ⟶ V) :
  ⟦F, G₁⟧.map iUV.op ≫ ihom_map_app F G₁ G₂ γ U =
  ihom_map_app F G₁ G₂ γ V ≫ (ihom_obj F G₂).map iUV.op :=
begin
  ext f W x,
  simp only [comp_apply, ihom_obj_map_apply, quiver.hom.unop_op, ihom_map_app_apply_app,
    ihom_map'_app_apply, restrict_subset_sections_map_app, restrict_subset_sections_map.app_apply],
  simp only [←comp_apply, category.assoc],
  rw [←γ.naturality],
  congr' 1,
end

/--
internal presheaf hom is functorial
-/
@[simps] def ihom_map (F G₁ G₂ : presheaf AddCommGroup.{u} X) (γ : G₁ ⟶ G₂) :
  ⟦F, G₁⟧ ⟶ ⟦F, G₂⟧ :=
{ app := λ U, ihom_map_app F G₁ G₂ γ U.unop,
  naturality' := λ U V iUV, by convert ihom_map_naturality F G₁ G₂ γ iUV.unop }

lemma ihom_map_id (F G : presheaf AddCommGroup.{u} X) :
  ihom_map F G G (𝟙 G) = 𝟙 _ :=
begin
  ext f U W x,
  simp only [ihom_map_app_2, ihom_map_app_apply_app, ihom_map'_app_apply, nat_trans.id_app,
    id_apply],
end

lemma ihom_map_comp (F G₁ G₂ G₃ : presheaf AddCommGroup.{u} X) (g₁₂ : G₁ ⟶ G₂) (g₂₃ : G₂ ⟶ G₃) :
  ihom_map F _ _ (g₁₂ ≫ g₂₃) = ihom_map F _ _ g₁₂ ≫ ihom_map F _ _ g₂₃ :=
begin
  ext f U W x,
  simp only [ihom_map_app_2, ihom_map_app_apply_app, ihom_map'_app_apply, nat_trans.comp_app,
    comp_apply],
end

/--
internal presheaf hom with source `F` is functorial

* obj level : `G ↦ ihom F G`
* map level : `α : G₁ ⟶ G₂`, a map `ihom F G₁ ⟶ ihom F G₂` is obtained by
  `U ↦ (f ↦ f ≫ α |_ U) `
-/
@[simps] def ihom (F : presheaf AddCommGroup.{u} X) :
  presheaf AddCommGroup.{u} X ⥤ presheaf AddCommGroup.{u} X :=
{ obj := ihom_obj F,
  map := ihom_map F,
  map_id' := ihom_map_id F,
  map_comp' := λ _ _ _, ihom_map_comp F _ _ _ }

end monoidal

end

end Top.presheaf

namespace Top.sheaf

open Top Top.presheaf topological_space
open category_theory category_theory.limits

universe u

variables {X : Top.{u}}

alias presheaf.monoidal.ihom_obj ← presheaf.ihom_obj

open_locale sheaf

lemma restrict_is_sheaf {F : Top.presheaf AddCommGroup.{u} X} 
  (hF : is_sheaf F) (U : opens X) :
  is_sheaf (F |_ U) :=
is_sheaf_of_open_embedding (Top.presheaf.emb.open_embedding U) hF

def sheaf_restrict (F : sheaf AddCommGroup.{u} X) (U : opens X) :
  sheaf AddCommGroup.{u} (Top.of U) := 
⟨_, restrict_is_sheaf F.cond U⟩

localized "infix (name := sheaf_restrict) `|_`:40 := Top.sheaf.sheaf_restrict" in sheaf

namespace monoidal

open opposite

lemma ihom_obj_is_sheaf_of_is_sheaf {F G : Top.presheaf AddCommGroup.{u} X}
  (hF : is_sheaf F) (hG : is_sheaf G) : is_sheaf ⟦F, G⟧ :=
sorry

open category_theory.grothendieck_topology

@[simps] def ihom_obj (F G : sheaf AddCommGroup.{u} X) : sheaf AddCommGroup.{u} X :=
{ val := ⟦F.val, G.val⟧,
  cond := ihom_obj_is_sheaf_of_is_sheaf F.cond G.cond }

localized "notation (name := sheaf_ihom_obj) `⟦`F, G`⟧` := 
  Top.sheaf.monoidal.ihom_obj F G" in sheaf

@[simps] def ihom (F : sheaf AddCommGroup.{u} X) :
  sheaf AddCommGroup.{u} X ⥤ sheaf AddCommGroup.{u} X :=
{ obj := λ G, ⟦F, G⟧,
  map := λ G₁ G₂ α, ⟨presheaf.monoidal.ihom_map _ _ _ α.val⟩,
  map_id' := λ G,
  begin
    ext U x y z,
    simp only [Sheaf.category_theory.category_id_val, presheaf.monoidal.ihom_map_app_2,
      presheaf.monoidal.ihom_map_app_apply_app, presheaf.monoidal.ihom_map'_app_apply,
      nat_trans.id_app, id_apply],
  end,
  map_comp' := λ G₁ G₂ G₃ α β,
  begin
    ext U x y z,
    simp only [Sheaf.category_theory.category_comp_val, presheaf.monoidal.ihom_map_app_2,
      presheaf.monoidal.ihom_map_app_apply_app, presheaf.monoidal.ihom_map'_app_apply,
      nat_trans.comp_app, comp_apply],
  end }

end monoidal

end Top.sheaf

namespace SHEAF_OF_MODULES

open topological_space opposite

variables {X : RINGED_SPACE} (M1 M2 : SHEAF_OF_MODULES X)

namespace monoidal

open Top.sheaf.monoidal

local attribute [instance] SHEAF_OF_MODULES.module_structure

@[simps] def smul_ihom_obj (U : (opens (↑X : TOP))ᵒᵖ) (r : X.presheaf.obj U)
  (s : (ihom_obj M1.ab_sheaf M2.ab_sheaf).1.obj U) : 
  (ihom_obj M1.ab_sheaf M2.ab_sheaf).1.obj U :=
{ app := λ V, 
      show M1.ab_sheaf.val.obj 
            (op ((Top.presheaf.emb.open_embedding U.unop).is_open_map.functor.obj V.unop)) ⟶ 
          M2.ab_sheaf.val.obj 
            (op ((Top.presheaf.emb.open_embedding U.unop).is_open_map.functor.obj V.unop)), 
      from let r' : X.presheaf.obj 
        (op ((Top.presheaf.emb.open_embedding U.unop).is_open_map.functor.obj V.unop)) := 
        X.presheaf.map (hom_of_le
          begin 
            rintros _ ⟨x, -, rfl⟩, exact x.2,
          end : (Top.presheaf.emb.open_embedding U.unop).is_open_map.functor.obj V.unop ⟶ U.unop).op r in
      r' • s.app V,
    naturality' := λ V V' i, 
    begin 
      dsimp,
      ext : 1,
      simp only [comp_apply, add_monoid_hom.smul_apply],
      erw [←comp_apply, s.naturality],
      erw M2.compatibility_bit,
      congr,
      rw [←comp_apply, ←X.presheaf.map_comp],
      refl,
    end }

instance has_smul_ihom_obj (U : (opens (↑X : TOP))ᵒᵖ) : 
  has_smul (X.presheaf.obj U) $ (ihom_obj M1.ab_sheaf M2.ab_sheaf).1.obj U :=
{ smul := smul_ihom_obj M1 M2 U }

lemma smul_ihom_obj.one_smul (U : (opens (↑X : TOP))ᵒᵖ) 
  (s : (ihom_obj M1.ab_sheaf M2.ab_sheaf).1.obj U) :
  smul_ihom_obj M1 M2 U 1 s = s :=
by ext; simp

lemma smul_ihom_obj.mul_smul (U : (opens (↑X : TOP))ᵒᵖ)
    (r r' : (X.presheaf.obj U))
  (s : (ihom_obj M1.ab_sheaf M2.ab_sheaf).1.obj U) :
  smul_ihom_obj _ _ _ (r * r') s = 
  smul_ihom_obj _ _ _ r (smul_ihom_obj _ _ _ r' s) :=
by ext V t; simp [mul_smul]

instance mul_action_ihom_obj (U : (opens (↑X : TOP))ᵒᵖ) : 
  mul_action (X.presheaf.obj U) $ (ihom_obj M1.ab_sheaf M2.ab_sheaf).1.obj U :=
{ one_smul := smul_ihom_obj.one_smul _ _ _,
  mul_smul := smul_ihom_obj.mul_smul _ _ _,
  ..SHEAF_OF_MODULES.monoidal.has_smul_ihom_obj M1 M2 U}

lemma smul_ihom_obj.smul_zero (U : (opens (↑X : TOP))ᵒᵖ) 
  (r : X.presheaf.obj U) :
  smul_ihom_obj M1 M2 U r 0 = 0 :=
by ext; simp

lemma smul_ihom_obj.smul_add (U : (opens (↑X : TOP))ᵒᵖ) 
  (r : X.presheaf.obj U)
  (x y : (ihom_obj M1.ab_sheaf M2.ab_sheaf).1.obj U) :
  smul_ihom_obj M1 M2 U r (x + y) = 
  smul_ihom_obj M1 M2 U r x + 
  smul_ihom_obj M1 M2 U r y :=
by ext; simp [smul_add]

instance distrib_mul_action_ihom_obj (U : (opens (↑X : TOP))ᵒᵖ) : 
  distrib_mul_action (X.presheaf.obj U) $ (ihom_obj M1.ab_sheaf M2.ab_sheaf).1.obj U :=
{ smul_zero := smul_ihom_obj.smul_zero _ _ _,
  smul_add := smul_ihom_obj.smul_add _ _ _,
  ..SHEAF_OF_MODULES.monoidal.mul_action_ihom_obj M1 M2 U}

lemma smul_ihom_obj.add_smul (U : (opens (↑X : TOP))ᵒᵖ) 
  (r r' : X.presheaf.obj U)
  (x : (ihom_obj M1.ab_sheaf M2.ab_sheaf).1.obj U) :
  smul_ihom_obj M1 M2 U (r + r') x = 
  smul_ihom_obj M1 M2 U r x + 
  smul_ihom_obj M1 M2 U r' x :=
by ext; simp [add_smul]

lemma smul_ihom_obj.zero_smul (U : (opens (↑X : TOP))ᵒᵖ) 
  (x : (ihom_obj M1.ab_sheaf M2.ab_sheaf).1.obj U) :
  smul_ihom_obj M1 M2 U 0 x = 0 :=
by ext; simp


instance module_ihom_obj (U : (opens (↑X : TOP))ᵒᵖ) : 
  module (X.presheaf.obj U) $ (ihom_obj M1.ab_sheaf M2.ab_sheaf).1.obj U :=
{ add_smul := smul_ihom_obj.add_smul _ _ _,
  zero_smul := smul_ihom_obj.zero_smul _ _ _,
  ..SHEAF_OF_MODULES.monoidal.distrib_mul_action_ihom_obj M1 M2 U}

lemma smul_ihom_obj_def (U : (opens (↑X : TOP))ᵒᵖ) 
  (r : X.presheaf.obj U)
  (x : (ihom_obj M1.ab_sheaf M2.ab_sheaf).1.obj U) :
  r • x = smul_ihom_obj _ _ _ r x := rfl

def ihom_obj : SHEAF_OF_MODULES X :=
{ ab_sheaf := ihom_obj M1.ab_sheaf M2.ab_sheaf,
  module_structure := SHEAF_OF_MODULES.monoidal.module_ihom_obj _ _,
  compatibility_bit := λ U V i r x, 
  begin 
    delta ihom_obj,
    ext W s, 
    dsimp only [smul_ihom_obj_def, smul_ihom_obj_app],
    rw [add_monoid_hom.smul_apply, Top.presheaf.monoidal.ihom_obj_map_apply,
      Top.presheaf.restrict_subset_sections_map_app,
      Top.presheaf.restrict_subset_sections_map.app_apply,
      smul_ihom_obj_app],
    dsimp,
    conv_rhs { rw [←comp_apply, ←X.presheaf.map_comp], },
    erw M2.compatibility_bit,
    rw [←comp_apply, ←X.presheaf.map_comp],
    refl,
  end }

@[simps] def ihom_map (F G₁ G₂ : SHEAF_OF_MODULES X) (α : G₁ ⟶ G₂) :
  ihom_obj F G₁ ⟶ ihom_obj F G₂ :=
{ ab_sheaf := (Top.sheaf.monoidal.ihom F.ab_sheaf).map α.ab_sheaf,
  map_smul := λ U r x, 
  begin 
    ext V s,
    dsimp [Top.presheaf.monoidal.ihom_map', smul_ihom_obj_def],
    rw [comp_apply, add_monoid_hom.smul_apply, comp_apply, ←α.map_smul],
  end }

@[simps] def ihom (F : SHEAF_OF_MODULES X) : 
  SHEAF_OF_MODULES X ⥤ SHEAF_OF_MODULES X :=
{ obj := ihom_obj F,
  map := ihom_map F,
  map_id' := λ G, 
  begin 
    ext1,
    exact (Top.sheaf.monoidal.ihom F.ab_sheaf).map_id _,
  end,
  map_comp' := λ G₀ G₁ G₂ α β, 
  begin 
    ext1,
     exact (Top.sheaf.monoidal.ihom F.ab_sheaf).map_comp _ _,
  end }

end monoidal

end SHEAF_OF_MODULES
