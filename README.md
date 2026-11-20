# Lean formalization of the corrected F-lattice paper

The pinned manuscript, its Julia constructor and the proof archives are in [paper](paper/README.md). The two main targets are the classification of integer superharmonic matrices and the standard and alternate recurrent odometers. [Campaign brief](CAMPAIGN.md) · [Formalization status](STATUS.md)

The sandbox repository is at /home/nitro/flattice-lean. Run flattice-lean on sandbox to open its agent. The active formalizer uses GPT-6.2 Sol at xhigh. The remote and local repositories store checkpoints on main. The older helper library is preserved in previous/ for comparison.

The toolchain is Lean 4.32.0. Run lake build from the repository root. Verify the manuscript snapshot with sha256sum -c paper.sha256.
