# Formalisation of Kloosterman sums and its related Character sums

This is the Mary Lister McCammon Fellowship for summer 2023, supervised by Prof. Kevin Buzzard. 
We provide the formalisation of the following main results in this repository : 
1. The definition of Kloosterman sum and its related elementary lemmas
2. The proof for the formula generic character sum :
   
   Let $q = p^{2\alpha}$ with $\alpha \geq 1$. Then we have
   
   $$ \sum_{x \in (\mathbb{Z}/p^{\alpha} \mathbb{Z})^* } \chi (f (x)) \psi (g (x)) = p^{\alpha}\sum_{{y \in (\mathbb{Z}/p^{\alpha} \mathbb{Z})^*}, \ h(y) \equiv 0 (\mathrm{mod} \ p^{\alpha}) } \chi{(f(y))} \psi{(g(y))} $$

   where $h(y)$ is the rational function given by

   $$ h(y) = ag'(y) + b \frac{f'}{f}(y) $$

   with the integers $a, b$ determined by the following equations
   
   $$\psi (x) = e(\frac{ax}{q}) \qquad \chi (1 + z p^\alpha) = e(\frac{bz}{p^\alpha})$$
   for some $ z \in (\mathbb{Z}/p^{\alpha} \mathbb{Z}) $

following the proof outlined in p 320 - 322 of the book Analytic Number Theory, Iwaniec and Kowalksi. 

The formula above can be specialised into the one for Kloosterman sum by choosing the appropriate form of for the rational functions $f$ and $g$. 

Please note that to limit to the formula , we also need the formalisation for the constant function $f$ 
The overall proof


It also contains the incomplete formalisation for the case when the power is odd (see `odd_char.lean`). But I hit the time limit before I could 


If I miss Lean a lot, I might come back to it again and complete the incomplete formalisation for the case when the power is odd. 
