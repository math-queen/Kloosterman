# Formalisation of Kloosterman sums and its related Character sums

I formalised the definition of Kloosterman sum and its related properties as a part of the project funded by the Mary Lister McCammon Fellowship for the summer of 2023, supervised by Prof. Kevin Buzzard. I provide the formalisation of the following main results in this repository : 
1. The definition of Kloosterman sum and its related elementary lemmas
2. The proof of the formula for the generic character sum :
   
   Consider the character sum of the form
   $$\sum_{x \in (\mathbb{Z}/q \mathbb{Z})^* } \chi (f (x)) \psi (g (x))$$
   where $\chi$ and $\psi$ are multiplicative and additive character respectively from $(\mathbb{Z}/q \mathbb{Z})^*$ to the units of complex and $f$ and $g$ are rational functions.
   
   Let $q = p^{2\alpha}$ with $\alpha \geq 1$. Then we have

   $$\sum_{x \in (\mathbb{Z}/p^{\alpha} \mathbb{Z})^* } \chi (f (x)) \psi (g (x)) = p^{\alpha}\sum_{{y \in (\mathbb{Z}/p^{\alpha} \mathbb{Z})^*}, \ h(y) \equiv 0 (\mathrm{mod} \ p^{\alpha}) } \chi{(f(y))} \psi{(g(y))}$$

   where $h(y)$ is the rational function given by
   
   $$h(y) = ag'(y) + b \frac{f'}{f}(y)$$
   
   with the integers $a, b$ determined by the following equations
   
   $$\psi (x) = e(\frac{ax}{q}) \qquad \chi (1 + z p^\alpha) = e(\frac{bz}{p^\alpha})$$
   where $e (n) := \exp (2 \pi i n)$ for some $z \in (\mathbb{Z}/p^{\alpha} \mathbb{Z})$.

   for the special case when the denominator and numerator of the function $f$ and $g$ can be expressed as non-constant polynomial and coprime to $p$. 

The formula above can be specialised into the one for Kloosterman sum by choosing the appropriate rational functions $f$ and $g$ (see p 322, Iwaniec and Kowalski). Please note that to derive the expression for Kloosterman sum from the above formula, we also need the formalisation for the case when both the denominator and numerator of the function $f$ can be expressed as constant function (which should be easier to be accomplished than the already formalised case when both the denominator and numerator are non-constant polynomial). 

This repository (`odd_char.lean`) also contains the incomplete formalisation for the case when the power is odd, i.e., $q = p^{2\alpha + 1}$ (see p 321, Iwaniec and Kowalski). But I hit the time limit before I could finish it off. If I miss Lean a lot, I might come back to it again and complete the half-done formalisation for the case when the power is odd. 
