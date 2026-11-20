# Integer superharmonic matrices on the F-lattice

This corrected edition uses the October 2023 manuscript in the final arXiv submission. Its source is identical to the last revised manuscript. The edition includes the figures, bibliography, mathematical supplements and the corrected Julia program. The submitted TeX source has SHA-256 `6a738707222f80ab4db6c08e623aa7f33709ccc32678c6c4744b6a810d34f3ab`. [Paper](farey_recursion.pdf) · [Manuscript source](farey_recursion.tex) · [Supplement on the Farey induction](Supplement/farey_induction.pdf)

## Changes to the paper

The edition retains 89.2% of the October 2023 manuscript’s nonblank, noncomment LaTeX lines verbatim. Sections 3, 4 and 7 and the pattern appendix match that submission word for word. The largest edits are the four staircase recurrence proofs in Section 6, the overlap argument at the end of Section 8, and the global proof in Section 9. Compared directly with the October 2021 working draft, 82.6% of its lines survive by the same measure. That comparison includes the revisions made between 2021 and 2023. Both counts include the new Section 9 in the main text and exclude the separate supplement. [Diff from the October 2021 working draft](paper-vs-2021.patch) · [Diff from the October 2023 submission](paper-changes.patch)

- Section 5 specifies the translation sign and the consistency condition on the additive constants when gluing partial odometers.
- Section 6 states the finite forbidden-set criterion, supplies its proof and corrects how a quarter-turn transports it. It restores a missing strip of the rotated alternate's domain, specifies the checkerboard of the reciprocal formulas, and replaces the four staircase recurrence arguments with explicit decreasing ranks. The rank formulas and proofs are reproduced in the supplement.
- Section 8 specifies the order of normalization on intersections and handles the two old sites where an incoming alternate is one unit higher. At each such site the older standard already gives the required height.
- Section 9 proves recurrence on the physical plane, identifies the finite tile heights in their actual insertion order, and uses the coverage of all period classes to pass from each finite tile to its periodic extension. It gives the growth calculation and distinguishes the two odometers modulo integer affine functions in their fixed coordinates. [Section 9 source](global_recurrence.tex) · [Manuscript diff from the submission](paper-changes.patch)

Parts I–III of the supplement identify the exact case lemmas on which Section 9 relies. Their full geometric arguments and arithmetic checks are included in the three accompanying archives. The base-case appendix reproduces the two complete rank calculations. [Plane fields](Supplement/standard-and-alternate-fields.zip) · [Ordered construction](Supplement/ordered-tile-construction.zip) · [Period coverage](Supplement/period-coverage.zip)

## Julia code

From this folder, run

~~~sh
julia --project=Code Code/run_code.jl 3312 patterns.svg
julia --project=Code Code/test/runtests.jl
julia --project=Code Code/audits/check_patterns.jl 4
~~~

The first command draws both standards and both alternates. It uses exact integer heights on the occupied coordinates and the true period increments at every seam. The package also exports tile heights as TSV, evaluates the height or Laplacian at a specified lattice site, and provides a matrix interface for existing scripts. Julia 1.7 or later is required. [Julia instructions](Code/README.md) · [Four-panel example](Code/examples/3312.svg)

The packaged tests passed 433 assertions on both Julia 1.7.1 and Julia 1.12.5, including the 37- and 44-two clipping examples. The depth-four check covered the empty word and all 120 nonempty words of length at most four, across all 484 standard and alternate outputs and 1,147,064 period classes. [Test results](Code/test/results/corrected-edition.txt) · [Published 37-two comparison](Code/test/results/published-word37.txt) · [Published 44-two failure](Code/test/results/published-word44.txt)

## Rebuilding the PDFs

Run the following from this folder with a TeX Live installation. The original bibliography is included in both BibTeX and typeset form.

~~~sh
latexmk -pdf farey_recursion.tex
(cd Supplement && latexmk -pdf farey_induction.tex)
~~~
