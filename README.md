# monoidal-nets
This is an Agda library developed for the formalisation of String Diagrams (Hypergraphs) along with proofs that they, with the usual operations, form a Symmetric Monoidal Category.

## Installation:

**Dependencies**: agda-stdlib (https://github.com/agda/agda-stdlib), agda-categories (https://github.com/agda/agda-categories)

To install this library:
1. Clone the repository into an empty folder, `PATH/TO/FOLDER`.
2. Rename the folder of the newly created repository from `oms567` to `monoidal-nets`
3. Navigate to your agda folder, `PATH/TO/AGDA` (normally this should be `~/.agda`) and add an extra line at the end of your `libraries` file containing: `PATH/TO/FOLDER/monoidal-nets/monoidal-nets.agda-lib` replacing `PATH/TO/FOLDER` by the actual path to the folder that the repository has been cloned into.
This will allow you to reference this library in other projects.

You should also add extra lines with paths to the dependency libraries' `.agda-lib` files, after downloading them, if they are not in `PATH/TO/AGDA/libraries` already.

Note: If you don't have a `.agda` folder or you don't know where it is try creating it using the command `mkdir ~/.agda`. Same for the libraries file: You can run `touch ~/.agda/libraries` to create it if it doesn't exist.


The library has been checked successfully using Agda version 2.6.1