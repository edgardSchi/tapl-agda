# Chapter 3

Chapter 3 contains 2 languages: B and NB.

## B Language

The B-Language has following syntax:

$$
\begin{align}
\textbf{t} ::= \ &true \\
&false \\
&if \ \textbf{t} \ then \ \textbf{t} \ else \ \textbf{t} \\
\textbf{v} ::= \ &true \\
&false \\
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
- Theorem 3.5.7: Every value is in normal form
- Theorem 3.5.8: If $t$ is in normal form, then $t$ is a value
- Theorem 3.5.11: Uniqueness of normal forms
- Theorem 3.5.12: Termination of evaluation

## NB Language

The NB-Language has following syntax:

$$
\begin{align}
\textbf{t} ::= \ &true \\
&false \\
&if \ \textbf{t} \ then \ \textbf{t} \ else \ \textbf{t} \\
&0 \\
&succ \ \textbf{t} \\
&pred \ \textbf{t} \\
&iszero \ \textbf{t} \\
\textbf{v} ::= \ &true \\
&false \\
&nv \\
\textbf{nv} ::= \ &0 \\
&succ \ \textbf{nv}
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

$$
\begin{prooftree}  
	\AxiomC{$t_1 \to t_1'$}
	\RightLabel{\ [E-SUCC]}
	\UnaryInfC{succ $t_1$ $\to$ succ $t_1'$}  
\end{prooftree}
$$

$$
\text{pred } 0 \to 0 \ [\text{E-PREDZERO}]
$$

$$
\text{pred (succ } nv_1 \text{)} \to nv_1 \ [\text{E-PREDSUCC}]
$$

$$
\begin{prooftree}  
	\AxiomC{$t_1 \to t_1'$}
	\RightLabel{\ [E-PRED]}
	\UnaryInfC{pred $t_1$ $\to$ pred $t_1'$}  
\end{prooftree}
$$

$$
\text{iszero} 0 \to true \ [\text{E-ISZEROZERO}]
$$

$$
\text{iszero (succ } nv_1 \text{)} \to false \ [\text{E-ISZEROSUCC}]
$$

$$
\begin{prooftree}  
	\AxiomC{$t_1 \to t_1'$}
	\RightLabel{\ [E-ISZERO]}
	\UnaryInfC{iszero $t_1$ $\to$ iszero $t_1'$}  
\end{prooftree}
$$

### Proofs

The following theorems and properties are proven:
- Exercise 3.5.14: Determincay of one-step evaluation
- Every value is in normal form
- Every numeric value is in normal form
- Uniqueness of normal forms
