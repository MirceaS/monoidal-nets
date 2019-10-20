# monoidal-nets
This is an agda library developed for the formalisation of Monoidal Hypernets and Hypergraphs used to model lambda calculus.

# Installation:
## Dependencies:
agda-categories (https://github.com/agda/agda-categories)

To install this library, clone the repository into an empty folder, `PATH/TO/FOLDER`. Then navigate to your agda folder, `PATH/TO/AGDA` (normally this should be `~/.agda`) and add an extra line at the end of your `libraries` file containing: `PATH/TO/FOLDER/monoidal-nets/monoidal-nets.agda-lib` replacing `PATH/TO/FOLDER` by the actual path to the folder that the repository has been cloned into. This will allow you to reference this library in other projects.
You should also add extra lines with paths to the dependency libraries' `.agda-lib` files, after downloading them, if they are not in already.
Note: If you don't have a .agda folder or you don't know where it is try creating it using the command `mkdir ~/.agda` and same for the libraries file: You can run `touch ~/.agda/libraries` to create it if it doesn't exist.


