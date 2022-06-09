# Chapter 3

Chapter 8 contains the typed NB-Language which adds typing rules to the [NB-Language](/TAPL/Chapter3/README.md) from chapter 3

## Typed NB Language

The Typed NB-Language has following typing syntax:

$$
\begin{align}
\textbf{T} ::= \ &Bool \\
&Nat \\
\end{align}
$$

And following typing rules:

$$
0 : \text{ Nat } \ [\text{T-ZERO}]
$$

$$
true : \text{ Bool } \ [\text{T-TRUE}]
$$

$$
false : \text{ Bool } \ [\text{T-FALSE}]
$$

$$
\begin{prooftree}  
	\AxiomC{$t_1$ : Bool}
	\AxiomC{$t_2$ : T}
	\AxiomC{$t_3$ : T}
	\RightLabel{\ [T-If]}
	\TrinaryInfC{if $t_1$ then $t_2$ else $t_3$ : T}  
\end{prooftree}
$$

$$
\begin{prooftree}  
	\AxiomC{$t_1$ : Nat}
	\RightLabel{\ [T-SUCC]}
	\UnaryInfC{succ $t_1$ : Nat}
\end{prooftree}
$$

$$
\begin{prooftree}  
	\AxiomC{$t_1$ : Nat}
	\RightLabel{\ [T-PRED]}
	\UnaryInfC{pred $t_1$ : Nat}
\end{prooftree}
$$

$$
\begin{prooftree}  
	\AxiomC{$t_1$ : Nat}
	\RightLabel{\ [T-ISZERO]}
	\UnaryInfC{iszero $t_1$ : Bool}
\end{prooftree}
$$

### Proofs

The following theorems and properties are proven:
- Lemma 8.2.2: Inversion of the typing relation
- Theorem 8.2.4: Uniqueness of types
- Lemma 8.3.1: Canonical form
- Theorem 8.3.2: Progress
- Theorem 8.3.3: Preservation
