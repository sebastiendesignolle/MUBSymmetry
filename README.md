# MUBSymmetryCode

Code corresponding to the paper 

"Mutually unbiased bases: polynomial optimization and symmetry"

by Sander Gribling and Sven Polak.

An update to the number of variables (improve the part to lexicographically reduce the monomials, including a transpose-check to reverse the order) was found after comparison with Erik Woodhead's code and after discussions with Stefano Pironio and Erik Woodhead. Many thanks to both Erik and Stefano.

It consists of four julia files:

-MUBWriteSDPA.jl
-ConstructReprSet.jl
-DetValMon.jl
-HelperFunctions.jl

A .dat-s (SDPA-input) file for the full symmetry reduced sdp using the wreath product Sd wr Sk can be generated using the function

MUBWriteSDPA(d,k,t,option)

Here t is an integer. The argument "option" is optional, the value option=1 corresponds to level t+1/2.

A .dat-s file (SDPA-input) for the submatrix corresponding to the first basis elements, using the group Sk, can be generated using the function 

MUBWriteSDPASk(d,k,t,option)

Here t is an integer. The argument "option" is optional, the value option=1 corresponds to level t+1/2.
