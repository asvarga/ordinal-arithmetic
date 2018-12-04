
# Ordinal Arithmetic

A (somewhat) verified Liquid Haskell implementation of ordinal arithmetic.

### Files

- **ordinals.hs** : Plain Haskell implementation
- **ordinals_LH.hs** : Liquid Haskell implementation 
- **Haskell.sublime-build** : Build file for LH with Sublime
- **NewProofCombinators.hs** : File copied from LH repo because of dependency issues

### Liquid Haskell

Functions expect the ordinal arguments to be in [Cantor Normal Form](https://www.wikiwand.com/en/Ordinal_arithmetic#/Cantor_normal_form). However, this can't be enforced with plain Haskell, so Liquid Haskell is required. 

LH is used to prove:

- the closure of Normal-Form Ordinals under
    - addition
    - subtraction
    - multiplication
- termination of all functions
- totality of all functions

To type-check refinements and proofs:

1. [Install LH](https://github.com/ucsd-progsys/liquidhaskell/blob/develop/INSTALL.md)
2. Run `liquid ordinals_LH.hs`

### TODO

- separate show
- prove closure under exponentiation
- decouple LH from main haskell (if possible)
- get LH to work properly with typeclasses (if possible)
    - get LH to understand casting of Ints to Ordinals with fromInteger
    - get rid of withProof variants and rename add' to add etc.
- silence [these warnings](https://github.com/ucsd-progsys/liquidhaskell/issues/1242) (if possible)
