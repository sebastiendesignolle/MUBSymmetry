# MUBSymmetryCode

Code corresponding to the paper 

"Mutually unbiased bases: polynomial optimization and symmetry"

by Sander Gribling and Sven Polak.

It consists of three julia files:

-MUBWriteSDPA.jl
-ConstructReprSet.jl
-DetermineValueMonomial.jl

An .dat-s (SDPA-input) file for the full symmetry reduced sdp using the wreath product Sd wr Sk can be generated using the function

MUBWriteSDPASymBlockDiagFULL(k,d,t,option)

Here t is an integer. The argument "option" is optional, the value option=2 corresponds to level t+1/2.
This function works at the moment up to level 5+1/2, because DetermineValueMonomial works for general monomials up to this degree. 
(The implemented symmetry reduction itself works for all degrees)

A .dat-s file (SDPA-input) for the submatrix corresponding to the first basis elements, using the group Sk, can be generated using the function 

MUBWriteSDPASymBlockDiagSk(k,d,t,option)

Here t is an integer. The argument "option" is optional, the value option=2 corresponds to level t+1/2.
This function works in general up to level 6+1/2, because DetermineValueMonomial works for monomials corresponding to first basis elements up to this degree.
For k at most 4 and d at most 6, the function DetermineValueMonomial (and hence the full function) works up to level 7+1/2.
(The implemented symmetry reduction itself works for all degrees)
