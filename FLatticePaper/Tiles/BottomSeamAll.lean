import FLatticePaper.Tiles.BottomSeam
import FLatticePaper.Tiles.SeamFieldsLowSymm
import FLatticePaper.Tiles.SeamSub
import FLatticePaper.Tiles.SeamCoverFinal

/-! Task Q25, the seam structures for every word: `BottomSeamOdd u` and `BottomSeamEven u` hold for every word `u`.

Each field is proved: `low` (`SeamFieldsLowSymm.low_odd`, `low_even`), `symm` (`symm_odd_field`, `symm_even_field`), `sub` (`SeamSub.subOdd_all`,
`subEven_all`), and `cover`, `nodup` (`SeamCoverFinal.coverNodupOdd_all`, `coverNodupEven_all`). -/

namespace FLatticePaper.Tiles.BottomSeamAll

open FLatticePaper FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.BottomSeam

theorem bottomSeamOdd_all (u : Word) : BottomSeamOdd u :=
  { low := SeamFieldsLowSymm.low_odd u
    symm := SeamFieldsLowSymm.symm_odd_field u
    sub := SeamSub.subOdd_all u
    cover := (SeamCoverFinal.coverNodupOdd_all u).cover
    nodup := (SeamCoverFinal.coverNodupOdd_all u).nodup }

theorem bottomSeamEven_all (u : Word) : BottomSeamEven u :=
  { low := SeamFieldsLowSymm.low_even u
    symm := SeamFieldsLowSymm.symm_even_field u
    sub := SeamSub.subEven_all u
    cover := (SeamCoverFinal.coverNodupEven_all u).cover
    nodup := (SeamCoverFinal.coverNodupEven_all u).nodup }

end FLatticePaper.Tiles.BottomSeamAll
