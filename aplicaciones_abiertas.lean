import .topologicos
import .cerrados
import tactic

open set
open function
open topologicos
open topologicos.espacio_topologico

variables {X Y : Type} [espacio_topologico X] [espacio_topologico Y]


def abierta (f : X → Y) := ∀ U : set X, abierto U → abierto (f '' U)

def cerrada (f : X → Y) := ∀ U : set X, cerrado U → cerrado (f '' U)

lemma homeo_sii_continua_y_abierta (f : X → Y) (hbij : bijective f) : homeomorfismo f ↔ continua f ∧ abierta f :=
begin
  split,
  {
    intro h,
    cases h with hcont hg,
    cases hg with g hgf,
    cases hgf with hgcont hginv,
    cases hginv with hgf hfg,
    split,
    {
      exact hcont,
    },
    {
      intros U hU,
      specialize hgcont U hU,
      suffices haux : f '' U = g ⁻¹' U ,
      {
        rw haux,
        exact hgcont,
      },
      {
        ext y,
        split,
        {
          intro hy,
          cases hy  with x hx,
          cases hx with hxU hxy,
          rw ← hxy,
          change (g ∘ f) x ∈ U,
          rw hgf,
          exact hxU,
        },
        {
          intro hy,
          use g y,
          split,
          {
            exact hy,
          },
          {
            change (f ∘ g) y = y,
            rw hfg,
            refl,
          }
        },
      },
    },
  },
  {
    intro hf,
    cases hf with hfcont hfab,
    split,
    {
      exact hfcont,
    },
    {
      cases hbij with hinj hsob,
      choose g hg using hsob,
      use g,
      split,
      {
        intros U hU,
        specialize hfab U hU,
        suffices haux : g ⁻¹' U = f '' U,
        {
          rw haux,
          exact hfab,
        },
        {
          ext y,
          split,
          {
            intro hy,
            specialize hg y,
            use g y,
            split,
              exact hy,
              exact hg,
          },
          {
            intro hy,
            cases hy with x hx,
            cases hx with hxU hxy,
            specialize hg y,
            suffices haux : g y = x,
            {
              rw ← haux at hxU,
              exact hxU,
            },
            {
              apply hinj,
              rw hg,
              rw hxy,
            },
          },
        },
      },
      {
        split,
        {
          ext x,
          apply hinj,
          specialize hg (f x),
          exact hg,
        },
        {
          ext y,
          apply hg,
        },
      },
    },
  },
end 

lemma  homeo_sii_continua_y_cerrada (f : X → Y) (hbij : bijective f) : homeomorfismo f ↔ continua f ∧ cerrada f :=
begin
  split,
  {
    intro hf,
    cases hf with hfcont heg,
    cases heg with g hg,
    cases hg with hgcont hginvf,
    cases hginvf with hgf hfg,
    split,
      exact hfcont,
    {
      intros C hC,
      rw continua_sii_preimagen_cerrado at hgcont,
      specialize hgcont C hC,
      suffices haux : f '' C = g ⁻¹' C,
      {
        rw haux,
        exact hgcont,
      },
      {
        ext y,
        split,
        {
          intro hy,
          cases hy with x hx,
          cases hx with hxC hxy,
          rw ← hxy,
          change (g ∘ f) x ∈ C,
          rw hgf,
          exact hxC,
        },
        {
          intro hy,
          use g y,
          split,
          {
            exact hy,
          },
          {
            change (f ∘ g) y = y,
            rw hfg,
            refl,
          },
        }
      },
    },
  },
  {
    intro h,
    cases h with hfcont hfcer,
    split, exact hfcont,
    {
      cases hbij with hinj hsup,
      choose g hg using hsup,
      use g,
      split,
      {
        intros U hU,
        suffices haux : g ⁻¹' U = f '' U,
        {
          rw haux,
          specialize hfcer Uᶜ,
          simp only [cerrado_def, compl_compl, abierto_def] at hfcer,
          specialize hfcer hU,
          suffices haux2 : (f '' Uᶜ)ᶜ = f '' U,
          {
            rw ← haux2,
            exact hfcer,
          },
          {
            ext y,
            split,
            {
              intro hy,
              use g y,
              split,
              {
                by_contradiction hneg,
                apply hy,
                use g y,
                split, exact hneg,
                apply hg,
              },
              {
                apply hg,
              },
            },
            {
              intro hy,
              cases hy with x hx,
              cases hx with hxU hxy,
              intro hneg,
              cases hneg with x' hx',
              cases hx' with hx'U hx'y,
              apply hx'U,
              rw ← hxy at hx'y,
              specialize hinj hx'y,
              rw hinj,
              exact hxU,
            },
          },
        },
        {
          ext y,
          split,
          {
            intro hy,
            use g y,
            split,
            {
              exact hy,
            },
            {
              apply hg,
            },
          },
          {
            intro hy,
            cases hy with x hx,
            cases hx with hxU hxy,
            have haux : g y = x,
            {
              rw ← hxy,
              apply hinj,
              apply hg,
            },
            {
              dsimp,
              rw haux,
              exact hxU,
            },
          },
        },
      },
      {
        split,
        {
          ext x,
          apply hinj,
          dsimp,
          apply hg,
        },
        {
          ext,
          apply hg,
        },
      },
    },
  },
end


lemma identidad_abierta : abierta (identidad : X → X) :=
begin
  intros U hU,
  simp only [identidad_def, image_id', abierto_def],
  exact hU,
end

lemma identidad_cerrada : cerrada (identidad : X → X) :=
begin
  intros C hC,
  simp only [identidad_def, image_id', cerrado_def, abierto_def],
  exact hC,
end

