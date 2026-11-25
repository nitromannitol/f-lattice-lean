# Comparator audit

Each pair has a `Challenge.lean`, which states a headline consumer of the odometers theorem with an intentional `sorry`, and
a `Solution.lean`, which proves the same statement from the repository. The official
[leanprover/comparator](https://github.com/leanprover/comparator) checks that the solution proves a statement whose
dependency closure matches the challenge's, that it uses only `propext`, `Quot.sound` and `Classical.choice`, and that the
replayed proof is accepted by the Lean kernel and by the independent nanoda kernel (`enable_nanoda`).

| Pair | Challenge | Solution |
| --- | --- | --- |
| hyperbola (`theorem:hyperbola`) | [Hyperbola/Challenge.lean](Hyperbola/Challenge.lean) | [Hyperbola/Solution.lean](Hyperbola/Solution.lean) |
| circle packing (`theorem:circle_packing`) | [CirclePacking/Challenge.lean](CirclePacking/Challenge.lean) | [CirclePacking/Solution.lean](CirclePacking/Solution.lean) |

The workflow is [comparator.yml](../.github/workflows/comparator.yml).
