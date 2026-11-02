[[Analysis of Alg.]]

### Definitions:

- Complex Number C  : A complex number represented as a tuple, a real part and an imaginary part (R, I)
- Samples S : A vector of size $N$ of complex numbers (C) where $N = 2^n$
- Twiddle $\omega$ :  The depiction of complex roots of unity $e^-\left( \frac{2\pi i}{N} \right)$
- DFT (S) : $DFT(S)[k] = \sum_{i < N} S[i] \times \omega^{ik}$
- FFT (S) :  pseudo-code below
```
FFT (S):
	if S.length == 1:
		return S
	else:
		let E be all the even elements of S
		let O be all the odd elements of S
		let E' be FFT(E)
		let O' be FFT(O) 
		
		for all k between 0 and len(O'):
			let O'' = O' * omega^k
		
		let top = []
		let bottom = []
		
		for k between 0 and N/2:
			top.append (E[k] + O''[k])
			
		for k between 0 and N/2:
			bottom.append (E[k] - O''[k])
		
		return [top + bottom]
```

### Lemmas:

1. $\omega^{N/2} = -1$
	- From  $\omega^{N/2} = e^{-(2\pi i(N/2) / N)}$
	- $= e^{-(2\pi i * 1/2)}$
	- $= e^{-\pi i}$
	- $= \cos(\pi) - i \sin(\pi)$ by Eulers Formula
	- $= -1 - i 0$ from Sin and Cos
	- $= -1$ 

2. $(\omega^2)^{N/2} = 1$
	- From $\omega = e^{-2\pi i/N}$ so $(w^2) = (e^{-2\pi i/N})^{2}$ 
	- $= e^{-(4\pi i)/N}$ so then $(\omega^2)^{N/2}= (e^{-(4\pi i)/N})^{N/2}$
	- $e^{-(4\pi i)/2} = e^{-2\pi i}$
	- $\cos\left( 2\pi \right) - i \sin\left( 2\pi \right)$ by Eulers Formula
	- 2 pi is one revolution instead of a half, so
	- $1 - i 0 = 1$ for all N that are powers of 2.

3. If $\lambda = e^{-(2\pi i)/M}$ and $\omega = e^{-(2\pi i)/N}$ then $\omega^2 = \lambda$ When $M = \frac{N}{2}$
	- $\omega^2 = e^{(-2\pi i/N)^2}$
	- $= e^{-(4\pi i)/N}$ which can be rewritten $e^{-(2\pi i)/\frac{N}{2}}$ 
	- and so $e^{-(2\pi i)/\frac{N}{2}} = \lambda = e^{-(2\pi i)/M}$ when $M = \frac{N}{2}$

4. For all the indices $j<\frac{N}{2}$ If we let E be the list of even elements of S $E = S[2j]$ and $O=S[2j+1]$ the odd elements, and then take the DFT of each to let $E' = DFT(E)$ and $O' = DFT(O)$ such that $E'[k] = \sum_{l<\frac{N}{2}}S[2l]*(\omega^2)^{lk}$ and $O'[k]=\sum_{l<\frac{N}{2}}S[2l+1]*(\omega^2)^{lk}$. Then, for all $k < N$ the sum of the kth element of E' with the product of the kth element of O' with the twiddle factor is equal to the kth element of the original DFT. $E'[k] + (\omega^k)O'[k] = DFT(S)[k]$
	- Starting backwards:
	- $DFT(S)[k] = \sum_{j < N}S[j] * \omega^{jk}$ by definition of DFT
	- $= \big(  \sum_{l < \left( \frac{N}{2} \right)} S[2l] * \omega^{(2l)k} \big) + \big(  \sum_{j<\left( \frac{N}{2} \right)} S[2j +1] * \omega^{(2j+1)k} \big)$ by simply reordering
	- $= \big(  \sum_{l < \left( \frac{N}{2} \right)} S[2l] * (\omega^2)^{lk} \big) + \big(  \sum_{j<\left( \frac{N}{2} \right)} S[2j +1] * \omega^{(2j+1)k} \big)$ by grouping powers
	- Specifically focusing on the second term,$\big(  \sum_{j<\left( \frac{N}{2} \right)} S[2j +1] * (\omega^2)^{jk}*\omega^k \big)$ because of the addition in the exponent. Which can be factored out as $\big( \omega^k * \sum_{j<\left( \frac{N}{2} \right)} S[2j +1] * (\omega^2)^{jk} \big)$
	- So together we have $= \big(  \sum_{l < \left( \frac{N}{2} \right)} S[2l] * (\omega^2)^{lk} \big) + \big( \omega^k * \sum_{j<\left( \frac{N}{2} \right)} S[2j +1] * (\omega^2)^{jk} \big)$
	- If we let some DFT $E'$ representing the DFT of the even elements of $S$ and we let some DFT $O'$ represent the DFT of the odd elements of S then 
	- $= E'[k] + (\omega^k * O'[k])$ by definition of DFT and by Lemma 3

5. If $M = \frac{N}{ 2}$, And $E'$ is the DFT of E as defined in Lemma 4, then $E'[k + M] = E'[k]$
	- $E'[k+M] = \sum_{j<M} S[2j] * \omega^{2j(k+M)}$ from the definition of $E'$ in Lemma 4
	- $= \sum_{j<M} S[2j] * (\omega^{2})^{j(k+M)} = \sum_{j<M} S[2j] * (\omega^2)^{jk}*(\omega^2)^{jM}$ by rules of powers
	- $= \sum_{j<M} S[2j] * (\omega^2)^{jk} * 1^j$ by Lemma 2! :D 
	- $= \sum_{j<M} S[2j] * (\omega^2)^{jk} = E'[k]$ by the definition above $E'[k]$ in Lemma 4.
	- We are just saying that the even elements of the signal repeat with periodicity M
			
6. If $M = \frac{N}{ 2}$, And $O'$ is the DFT of O as defined in Lemma 4, then $O'[k + M] = O'[k]$
	- This is almost exactly the same proof as above, except for the odd elements. The same math and lemmas apply. 


### Claiming Some Stuff
- Claim A: 
	- By Lemma 4: $DFT(S)[k] = E'[k] + (\omega^k)O'[k]$  holds for all $K < \frac{N}{2}$ 
	- This is the Top half
- Claim B:
	- Also by Lemma 4: if $M = \frac{N}{2}$, then $DFT(S)[k+M] = E'[k +M] + (\omega^{k+M})O'[k+M]$ for all $k < \frac{N}{2}$
	- applying Lemma 5  and 6 to E' and O' : $= E'[k] +  (\omega^{k+M})O'[k]$
	- $= E'[k] +  (\omega^{k}*\omega^{M})O'[k]$ by rules of powers. 
	- $= E'[k] +  (\omega^{k}*-1)O'[k]$ by Lemma 1
	- thus, $DFT(S)[k + M] = E'[k] -  (\omega^{k})*O'[k]$
	- this is the bottom half. 

### Theorem:

For every $S$ of size $N = 2^n$, and $n \geq 0$,  $FFT(S) = DFT(S)$
### Proof:
- By induction:
	- Base case : n = 0:
		- Then $FFT(S) \to S$ and $DFT(S) \to \sum_{1}S_{1} * \omega^0$
		- $= S*\omega^0$ The sum of only a single element is that element.
		- $S * 1 = S$ Anything to power 0 is 1
		- $S = S$
	- Induction step : n >= 1
		- assume $FFT(S) = DFT(S)$ for all $N = 2^{n-1}$ as the induction hypothesis.
		- let $E$ be a list of all the even elements of $S$ such that for all $k< \frac{N}{2}$, $E[k] = S[2k]$
		- let $O$ be a list of all the odd elements of $S$ such that for all $k< \frac{N}{2}$, $O[k] = S[2k+1]$
		- The length of both $E$ and $O$ is $M = \frac{N}{2}$ by construction
		- Then let $E' = FFT(E) = DFT(E)$ and $O' = FFT(O) = DFT(O)$ both by the induction hypothesis.
		- For each index $j$ between $0$ and $N$:
			- When the index $j < M$ Then $FFT(S)[j] = E'[j] +\omega^j *O'[j]$ 
				- (So $FFT(S)[k] = DFT(S)[k]$ for all $0 \leq k \lt M$ by Claim A and  Lemma 5)
			- When the index $j \geq M$ Then $FFT(S)[j-M] = E'[j-M] - \omega^j * O'[j-M]$
				- (So $FFT(S)[k] = DFT(S)[k]$ for all $M \leq k < N$) by Claim B and Lemma 6
			- For all $k$ between $0$ and $N$, either $k<M$ or $M\leq k <N$ So $FFT(S)[k] = DFT(S)[k]$ For all $k$
			- Therefore $FFT(S) = DFT(S)$
