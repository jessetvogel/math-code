# Counting representations

These scripts compute the representation theory of the groups $\mathbb{U}_n$ of unipotent matrices, and $\mathbb{T}_n$ of upper triangular matrices, over finite fields $\mathbb{F}_q$. The representation theory of such a group $G$ is encoded in the *representation zeta function* $\zeta_G(s) = \sum_{\chi \in \hat{G}} \chi(1)^{-s}$, where $\hat{G}$ denotes the set of complex irreducible characters of $G$.



From these representation zeta functions, the $E$-polynomials of the *$G$-representation varieties* $R_G(\Sigma_g) = \text{Hom}(\pi_1(\Sigma_g), G)$ can be determined as $e(R_G(\Sigma_g)) = e(G)^{2g - 1} \zeta_G(2g - 2) \in \mathbb{Z}[u, v]$, where $q = uv$.

