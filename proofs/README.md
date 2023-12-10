# Contents

A Coq description of the ARM-Toy memory model can be found in the file `armtoy/formal_proofs2.v`. Build Hahn before running.

An old version `armtoy/formal_proofs.v` also exists. The difference is that it does not use the Hahn library for relations but instead model relations using `ListSets`. It is also missing a few proofs.

# How to build Hahn

Download submodule `hahn` and follow build instructions.

To build the whole ARM-Toy project, run `make` in `armtoy/`.
