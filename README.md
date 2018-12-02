

# Ordinal Arithmetic

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

### TODO

- prove closure under exponentiation
- organize
    - pull important refinements to top of file?
- get LH to work better with typeclasses
    - instance Num NFOrd where ...
    - instance Ord NFOrd where ...
    - get LH to understand casting of Ints to Ordinals with fromInteger
