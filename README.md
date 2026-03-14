This repository contains the exercises for a mini-workshop at McMaster University on learning Lean "for the working mathematician". 
It is based on Patrick Massot's [Glimpse of Lean](https://github.com/PatrickMassot/GlimpseOfLean/tree/master#).
We strongly recommend following the instructions below to set up a copy of this project on your local machine, following the [community instructions](https://leanprover-community.github.io/install/project.html#working-on-an-existing-project).

## Set up this project on your local machine

1. Download VS Code and Lean by following the [official instructions](https://lean-lang.org/install/)
2. Make sure you have [git](https://git-scm.com/) installed. You may want to restart your computer afterwards.
3. Open a terminal in the directory where you would like this project to live (on Windows you can use file explorer to navigate to this directory, then right click -> open terminal). You do not need to create a new folder. The next commands will create a subfolder named `GlimpseOfLean` in the chosen directory.
4. Run `git clone https://github.com/Mathias-Stout/GlimpseOfLean.git`
5. Run `cd GlimpseOfLean`. This moves you inside the newly created `GlimpseOfLean` folder.
6. Run `lake exe cache get`. This will prevent your editor from rebuilding the entire Mathlib when opening this project (which could take a very long time).
7. Launch VS Code by running `code .` (mind the dot).
8. Alternatively, you may run VS Code from your application menu. Then choose the option "Open folder" and choose the folder `GlimpseOfLean` (_not_ one of its subfolders).

### Updating the exercise set


1. Open a terminal in the folder `GlimpseOfLean`
2. Run `git fetch`.
3. Run `git pull`.

## Exercises

**note**: these exercise files may be updated until the start of the workshop. If you want to play around with these beforehand, it is recommended to either work on a separate git branch, or create a manual copy of this project (don't forget to run `lake exe cache get` in the copied folder before opening it in VS Code).

The exercises **01-04** will guide you through handling basic logical operations. Depending on your familiarity with Lean, you may elect to go through these in detail, or refer back to them when relevant.

Depending on the area of mathematics you are most familiar with, you may then want to try one of the exercises in the `Topics` folder. We recommend either

* `ClassicalPropositionalLogic.lean`: prove soundness of classical propositional logic.
* `RingTheory.lean`: prove the first isomorphism theorem and Chinese remainder theorem for commutative rings.
*  `SequenceLimits.lean`: prove results from analysis about sequences and their limits. In particular, show that every cluster point of a Cauchy sequence is a limit of the sequence.

More exercises and area-specific projects will be added before the start of the workshop.

There is also the `shorter.lean` file: it fast-tracks you through some of the basics of files 01-04 and culminates with a not-entirely trivial statement on limits of sequences.
