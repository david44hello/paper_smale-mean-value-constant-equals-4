/-
Solution.lean — the proved forms of the three theorems of `Challenge.lean`, for the Palomar registry.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
-/
module

public import Smale

/-!
# Smale's mean value constant equals 4: the proofs

This module imports the whole proof development (`Smale`) and adds nothing. The development itself declares, under the
same names and with the same statements as `Challenge.lean`:
* the definitions `Smale.IsPd`, `Smale.critRatios`, `Smale.mval`, `Smale.Kd`, `Smale.Kstar`
  (in `Smale/Defs/Basic.lean`) and `Smale.P030.Rows.IsPdGen`, `critRatiosGen`, `Sval`, `KdGen`, `KstarGen`
  (in `Smale/P030/Rows/DefsGen.lean`);
* the theorems `Smale.P030.kstar_eq_four` and `Smale.P030.tendsto_Kd_four` (in `Smale/P030/Contract.lean`) and
  `Smale.P030.Rows.thm_1_1` (in `Smale/P030/Rows/Thm11.lean`), proved there from the axioms `propext`,
  `Classical.choice` and `Quot.sound` alone.

`lake comparator` (configuration `comparator.json`) checks that each of these declarations is the same here as in
`Challenge.lean`, and that the three proofs use only those three axioms.
-/
