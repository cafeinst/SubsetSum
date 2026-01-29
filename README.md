DOI 10.5281/zenodo.18332961

# SubsetSum

This repository contains a formal Isabelle/HOL development concerning
information-flow lower bounds for SUBSET–SUM and a conditional implication
of ¬(P = NP) under an explicit hypothesis called LR-read.

## Contents

- `SubsetSum_DecisionTree/`  
  Abstract reader-style decision-tree lower bounds.

- `SubsetSum_CookLevin/`  
  Transfer of reader-style bounds to Cook–Levin Turing machines.

- `SubsetSum_PneqNP_Conditional/`  
  Conditional ¬(P = NP) implication under LR-read.

All theories compile in Isabelle/HOL.

## What is the LR-read hypothesis?

LR-read is an explicit information-flow assumption about how a SUBSET–SUM solver
acquires and distinguishes numerical information. Informally, it requires that,
for some canonical split of the SUBSET–SUM verification equation, the solver’s
observable behaviour distinguishes all possible left-hand and right-hand candidate 
values individually arising from that split.

This assumption is reasonable in the same sense as the information-access
restrictions used in many standard lower-bound models. When correctness
depends on ruling out exponentially many competing numerical possibilities,
some form of per-candidate distinction must be reflected in the solver’s
observable behaviour. LR-read makes this requirement explicit, without
restricting the internal computations a solver may perform.

## Citation

If you use or reference this development, please cite:

Craig Alan Feinstein, *Information-Flow Lower Bounds for SUBSET–SUM*,  
Zenodo, 2026.  
DOI: https://doi.org/10.5281/zenodo.18332961
