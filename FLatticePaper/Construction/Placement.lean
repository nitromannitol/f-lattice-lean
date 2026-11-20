import FLatticePaper.Construction.OrderedOverlap
import FLatticePaper.Graph
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Group.Prod
import Mathlib.Data.Prod.Lex

namespace FLatticePaper.Construction.HeightTile

private def offsetEmbedding (offset : Site) : Site ↪ Site where
  toFun site := site + offset
  inj' := fun _ _ => add_right_cancel

private theorem mem_map_offset_iff (sites : Finset Site) (offset dest : Site) :
    dest ∈ sites.map (offsetEmbedding offset) ↔ dest - offset ∈ sites := by
  constructor
  · intro h
    obtain ⟨site, hsite, rfl⟩ := Finset.mem_map.mp h
    simpa only [offsetEmbedding, Function.Embedding.coeFn_mk, add_sub_cancel_right] using hsite
  · intro h
    exact Finset.mem_map.mpr ⟨dest - offset, h, sub_add_cancel dest offset⟩

/-- Translate all occupied sites and evaluate the height slope at the destination. -/
def place (tile : HeightTile Site) (offset slope : Site) : HeightTile Site where
  sites := tile.sites.map (offsetEmbedding offset)
  height site :=
    tile.height ⟨site.val - offset, (mem_map_offset_iff _ _ _).mp site.property⟩ +
      (slope.1 * site.val.1 + slope.2 * site.val.2)

theorem mem_place_sites (tile : HeightTile Site) (offset slope dest : Site) :
    dest ∈ (tile.place offset slope).sites ↔ dest - offset ∈ tile.sites :=
  mem_map_offset_iff tile.sites offset dest

theorem place_sites_nonempty (tile : HeightTile Site) (offset slope : Site)
    (hne : tile.sites.Nonempty) : (tile.place offset slope).sites.Nonempty :=
  hne.map

theorem place_height_at_add (tile : HeightTile Site) (offset slope : Site) (site : tile.sites) :
    (tile.place offset slope).height ⟨site.val + offset,
      (tile.mem_place_sites offset slope _).mpr (by simpa only [add_sub_cancel_right] using site.2)⟩ =
      tile.height site + (slope.1 * (site.val + offset).1 + slope.2 * (site.val + offset).2) := by
  have heq : (⟨site.val + offset - offset, (tile.mem_place_sites offset slope _).mp
    (Finset.mem_map.mpr ⟨site.val, site.property, rfl⟩)⟩ : tile.sites) = site :=
    Subtype.ext (add_sub_cancel_right _ _)
  exact congrArg (fun src => tile.height src +
    (slope.1 * (site.val + offset).1 + slope.2 * (site.val + offset).2)) heq

theorem Agrees.place {tile : HeightTile Site} {target : Field} {gauge : ℤ}
    (h : tile.Agrees target gauge) (offset slope : Site) :
    (tile.place offset slope).Agrees
      (fun site => target (site - offset) + (slope.1 * site.1 + slope.2 * site.2)) gauge := by
  intro site
  change tile.height ⟨site.val - offset, (tile.mem_place_sites offset slope _).mp site.property⟩ +
    (slope.1 * site.val.1 + slope.2 * site.val.2) =
    target (site.val - offset) + (slope.1 * site.val.1 + slope.2 * site.val.2) + gauge
  rw [h ⟨site.val - offset, (tile.mem_place_sites offset slope _).mp site.property⟩]
  dsimp only
  omega

private def rowKey (site : Site) : ℤ ×ₗ ℤ := toLex (site.2, site.1)

private def siteOfRowKey (value : ℤ ×ₗ ℤ) : Site := ((ofLex value).2, (ofLex value).1)

/-- The leftmost occupied site in the lowest occupied row. -/
def lowerLeft (tile : HeightTile Site) (hne : tile.sites.Nonempty) : Site :=
  siteOfRowKey ((tile.sites.image rowKey).min' (hne.image _))

/-- The rightmost occupied site in the highest occupied row. -/
def upperRight (tile : HeightTile Site) (hne : tile.sites.Nonempty) : Site :=
  siteOfRowKey ((tile.sites.image rowKey).max' (hne.image _))

theorem lowerLeft_mem (tile : HeightTile Site) (hne : tile.sites.Nonempty) :
    tile.lowerLeft hne ∈ tile.sites := by
  obtain ⟨site, hsite, heq⟩ := Finset.mem_image.mp
    (Finset.min'_mem _ (hne.image rowKey))
  unfold lowerLeft
  rw [← heq]
  exact hsite

theorem upperRight_mem (tile : HeightTile Site) (hne : tile.sites.Nonempty) :
    tile.upperRight hne ∈ tile.sites := by
  obtain ⟨site, hsite, heq⟩ := Finset.mem_image.mp
    (Finset.max'_mem _ (hne.image rowKey))
  unfold upperRight
  rw [← heq]
  exact hsite

/-- The coordinatewise minima, which need not form an occupied site. -/
def boxOrigin (tile : HeightTile Site) (hne : tile.sites.Nonempty) : Site :=
  ((tile.sites.image Prod.fst).min' (hne.image _), (tile.sites.image Prod.snd).min' (hne.image _))

/-- The constructor's rectangular trim, with no change of height gauge. -/
def trim (tile : HeightTile Site) (hne : tile.sites.Nonempty) : HeightTile Site :=
  tile.place (-tile.boxOrigin hne) 0

/-- The lower-left normalization used before a tile is placed as a new source. -/
def llCenter (tile : HeightTile Site) (hne : tile.sites.Nonempty) : HeightTile Site :=
  tile.place (-tile.lowerLeft hne) 0

theorem zero_mem_llCenter (tile : HeightTile Site) (hne : tile.sites.Nonempty) :
    (0 : Site) ∈ (tile.llCenter hne).sites := by
  rw [llCenter, mem_place_sites, sub_neg_eq_add, zero_add]
  exact tile.lowerLeft_mem hne

theorem trim_sites_nonempty (tile : HeightTile Site) (hne : tile.sites.Nonempty) :
    (tile.trim hne).sites.Nonempty :=
  tile.place_sites_nonempty _ _ hne

theorem Agrees.trim {tile : HeightTile Site} {target : Field} {gauge : ℤ}
    (h : tile.Agrees target gauge) (hne : tile.sites.Nonempty) :
    (tile.trim hne).Agrees (fun site => target (site + tile.boxOrigin hne)) gauge := by
  change (tile.place (-tile.boxOrigin hne) 0).Agrees _ _
  simpa [sub_neg_eq_add] using h.place (-tile.boxOrigin hne) 0

end FLatticePaper.Construction.HeightTile
