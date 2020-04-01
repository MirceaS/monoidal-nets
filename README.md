# monoidal-nets
This is an Agda library developed for the formalisation of String Diagrams along with proofs that they, with the usual operations, form a Symmetric Monoidal Category.

**This library uses the K axiom and the --safe flag.**

## Installation:

**Dependencies**: agda-stdlib (https://github.com/agda/agda-stdlib), agda-categories (https://github.com/agda/agda-categories)

To install this library in some folder `PATH/TO/FOLDER`, run the following commands:
1. `cd PATH/TO/FOLDER`
2. `git clone https://git-teaching.cs.bham.ac.uk/mod-ug-proj-2019/oms567.git`
3. Rename the repository folder from `oms567` to `monoidal-nets`
4. `mkdir -p ~/.agda`
5. `echo "PATH/TO/FOLDER/monoidal-nets/monoidal-nets.agda-lib" >> ~/.agda/libraries`

This will allow you to reference this library in other projects.

Make sure that you also have installed the libraries that the project depends on, mentioned above. The process of installing them is very similar to the above and instructions can be found on the respective GitHub pages.

To check that everything is okay, open `Check.agda` in Emacs mode and load it. It should type check successfully.
If any error comes up please submit an Issue on this GitHub page.

*Note: For some users, the default Agda folder may be located somewhere else (not in `~/.agda`). If that happens to be the case, please change the commands above accordingly.*


The library has been checked successfully using Agda version 2.6.1
