# Chapter 3

Chapter 3 contains 2 languages: B and NB.

## B Language

The B-Language has following syntax:

$$
\begin{align}
\textbf{t} &::= true \ | \ false \ | \ if \ \textbf{t} \ then \ \textbf{t} \ else \ \textbf{t} \\
\textbf{v} &::= true \ | \ false
\end{align}
$$

And following evaluation rules:

$$
\text{if true then } t_2 \text{ else } t_3 \to t_2 \ [\text{E-IfTrue}]
$$

$$
\text{if false then } t_2 \text{ else } t_3 \to t_3 \ [\text{E-IfFalse}]
$$

$$
\begin{prooftree}  
	\AxiomC{$t_1 \to t_1'$}
	\RightLabel{\ [E-If]}
	\UnaryInfC{if $t_1$ then $t_2$ else $t_3$ $\to$ if $t_1'$ then $t_2$ else $t_3$}  
\end{prooftree}
$$

### Proofs

The following theorems and properties are proven:
- Theorem 3.5.4: Determincay of one-step evaluation
- Theorem 3.5.11: Uniqueness of normal forms
