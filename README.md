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


\subsection{Remarks on the implementation}
\begin{remark} 
We mention a bijection (used in the code) between the set of pairs $(\bm j, \bm \tau)$ with $|\bm j^{-1}(a)| = |\Lambda^a|$ for $a \geq 2$, $\bm \tau \in \bm T^k_{\underline \Lambda, \underline \gamma}$ and a set of tuples of semistandard tableaux that we define now. Let $\bm T^{k}_{\underline \Lambda,r}$ be the set of tuples of semistandard young tableaux~$\bm{\tau}' = (\tau_1', \ldots, \tau_\ell')$ so that each~$\tau_a'$ is of shape~$\Lambda^a$ and such that~$\tau_1'$ contains~$k-r$ times symbol~$1$ and all tableaux in the tuple~$\bm{\tau}'$ together contain 1 time symbols~$2,\ldots, r+1$ each. The bijection assigns to a pair $(\bm j, \bm \tau)$ the element $\bm \tau' \in \bm T^{k}_{\underline \Lambda,r}$ for which $\tau'_1$ is obtained from $\tau_1$ by replacing each symbol $i+1$ by the $i$th smallest element of $\bm j^{-1}(1)$ plus $1$. For $a \geq 2$, $\tau'_a$ is obtained from $\tau_a$ by replacing each symbol $i$ by the $i$th smallest element of $\bm j^{-1}(a)$ plus $1$.
\end{remark}

\begin{remark}  
Let us write, using the function~$\psi_P$ from \cref{computationremark} and $\bm \tau \in \bm T^k_{\underline \Lambda,r}$,  
$v_{\sigma_i,Q_i} := \psi_{Q_i} \left( \sum_{\sigma_i' \sim \sigma_i} \sum_{c_i \in C_{\nu_{j(i)}}} \mathrm{sgn}(c_i) (c_i \cdot \sigma_i')\right)$
and $u_{\tau,P} := \psi_P\left(\bigotimes_{a=1}^\ell \sum_{\tau_a' \sim \tau_a} \sum_{d_a \in C_{{\Lambda^a}}} \mathrm{sgn}(d_a)  (d_a \cdot \tau_a')\right)$. Then $u_{(\bm \sigma, \bm \tau),(P,{\bm Q})}= \mathrm{Perm}_P \left(\bigotimes_{i=1}^r v_{\sigma_i,Q_i}  \right) \otimes u_{\tau,P}$, which is the description of the representative vectors we use in our implementation.
\end{remark} 
