Lean verification work in progress

This directory currently contains ordinary reusable proof infrastructure.
The exact author-facing F-lattice definitions and main theorem interface
remain under review; nothing here imports or assumes an unproved main
classification theorem. These helper results do not constitute a completed
formalization of the paper.

Compile a module from the parent workspace with:

    python3 lean/check.py FLattice/Auxiliary/Ceiling.lean

The launcher uses the exact Lean4.32.0 executable and cached mathlib revision
in ../lean_environment_inspection.json. It only writes project build files
under this directory and does not update or rebuild the external cache.
Compile project dependencies before their consumers.

No sorry, admit, project axiom, native_decide or heartbeat override is allowed
in these implementation modules. The main theorem is still unproved.
