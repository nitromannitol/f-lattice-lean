import FLatticePaper.Plane.Induction.TwosPriceE

/-! Checks for task 72 (the price range of the twos base: the explicit price and the closed-polygon key): the axioms are standard. -/
/--
info: 'FLatticePaper.Induction.sq_div4_add' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.sq_div4_add

/--
info: 'FLatticePaper.Induction.twos_cutPrice' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.twos_cutPrice

/--
info: 'FLatticePaper.Induction.twos_price_unfold' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.twos_price_unfold

/--
info: 'FLatticePaper.Induction.twos_E_key' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.twos_E_key
