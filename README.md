# Formalisation of Kloosterman sums and its related Character sums

This is the Mary Lister McCammon Fellowship for summer 2023, supervised by Prof. Kevin Buzzard. 
We provide the formalisation of the following main results in this repository : 
1. The definition of Kloosterman sum and its related elementary lemmas
2. The proof for the formula generic character sum
$ 1 = 1 $

$$ \sum_{x \in (\mathbb{Z}/p^{\alpha} \mathbb{Z})^*} \chi (f (x)) \psi (g (x)) = p^{\alpha}\psum_{\substack{y \in (\mathbb{Z}/p^{\alpha} \mathbb{Z})^* \\ h(y) \equiv 0 (\mathrm{mod} \, p^{\alpha}) }} \chi{(f(y))} \psi{(g(y))} $$



$$ {\sideset{}{^*}\sum}_{x(\mathrm{mod} \, q)} \chi (f (x)) \psi (g (x)) = $$
for multiplicative character $\chi$ and additive character $\psi$ for the even case when the g

following the proof outlined in the book Analytic Number Theory, Iwaniec and Kowalksi. 

By choosing the appropriate form of for the rational functions $f$ and $g$, we can specialise the formula above into the one for Kloosterman sum and derive a formula for the Kloosterman sum 

Please note that to limit to the formula , we also need the formalisation for the constant function $f$ 
The overall proof


It also contains the incomplete formalisation for the case when the power is odd (see `odd_char.lean`). But I hit the time limit before I could 


If I miss Lean a lot, I might come back to it again and complete the incomplete formalisation for the case when the power is odd. 
