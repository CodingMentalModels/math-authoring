# math-authoring

Goal: Create a user friendly authoring system for doing math, which allows the user to:
- Define mathematical types, objects, and predicates.
- Define allowable transformations on those types, objects, and predicates.
- Hypothesize statements and transform them.
- Export to LaTeX.
- Specify a desired end state and use a search algorithm to find the transformations to get there.


## Key Ideas
- We aren't trying to create a proof system / proof assistant.  We're trying to create a helpful tool for performing mathematical manipulations, analogous to a word processor for writing or an IDE for coding.
- To do this, we'll use quantified first order logic over a type system that has some templatization (analogous to generics).  
- Whenever we're tempted to say $\forall x \in X \enspace x \in P$ or $\forall x \in X \enspace P(x)$ where $X$ is some `Type` and $P$ is some property or predicate, we can instead say $\forall x \in X \enspace \exists p \in P \enspace x = p$.  
- Allowing users to specify which transformations are allowable in their system provides a lot of flexibility and punts the correctness, completeness, etc. of the system to the user.
- Predefining some objects, types, transformations is nice, similar to the standard library in a programming language.

## User Stories

### Simple Arithmatic

$$
\frac{53!}{52! + 51!} = \frac{53 \cdot 52 \cdot 51!}{51!(52 + 1)} = \frac{53 \cdot 52}{52 + 1} = 52
$$

To do this, we'd leverage built-in types:
- Natural numbers would automatically convert to a type $53$, $52$, etc. which contains exactly that value.
- $+$, $\cdot$, and $\frac{\cdot}{\cdot}$ would all be predicates defined by their axioms.  e.g. there would be allowed transformations like:

$$
x \in \mathbb{Z} \implies \enspace \exist e \in \mathbb{Z} \enspace x + e = x
$$

- Similarly, factorial ($!$) would be defined by a transformation:

$$
0! = 1 \\
\forall x \in \mathbb{Z} \enspace x > 0 \implies x! = (x - 1)! \cdot x
$$

The engine would know how to evaluate arithmetic expressions by default (although in principle these could also be done via axioms), so the steps here would be something like:

1. Hypothesize:
$$
x \in 51, y \in 52, z \in 53
$$

2. From the definition of $!$, generate statements that $x! \in \mathbb{Z}$.  Note that the actual statement would be $\exists a \in \mathbb{Z} \enspace x! = a$.  (Relies on $51, 52, 53 \subset \mathbb{Z}$)

3. From the definition of the arithmetic operations, generate statements that $\frac{53!}{52! + 51!} \in \mathbb{Z}$.  Similarly, this would instantiate a new variable, but this could be swept under the rug by the UI.

4. Perform transformations based on the various definitions to reduce the fraction.

5. Evaluate $\frac{53 \cdot 52}{52 + 1}$.  

This obviously seems very tedious, but **a lot** of it can be hidden from the user.  e.g. $x, y, z$ need never be shown the user.  Same with the "temporary variables" used to store the intermediate values.

### Algebra

$$
\frac{x^2}{x^4 + 1} = 1/7 \\
7x^2 = x^4 + 1 \\
x^4 - 7x^2 + 1 = 0 \\
x^2 = \frac{7 \pm \sqrt{45}}{2}
$$

### Proofs

#### Direct

Hypothesize:
$$
a, b \in \mathbb{2Z}
$$

Then using the definition of $2\mathbb{Z}$ and facts about arithmetic:

$$
\exists c, d \in \mathbb{Z} \enspace 2c = a \land 2d = b \\
a + b = 2c + 2d \\
a + b = 2(c + d) \\
a + b \in 2\mathbb{Z}
$$

#### By contradiction

Hypothesize:
$$
|\{p | p \text{ is prime}\}| < \infty
$$

Then, unpacking definitions and using facts from arithmatic:
$$
q := \prod p + 1 \in \mathbb{Z} \land q \not \in P \land q > p \\
\forall p \in P \enspace q \bmod{p} \equiv 1 \\
\forall p \in P \enspace p \nmid q \\
q \text{ is prime} \\
q \in P \\
\bot \\
$$

Therefore the inverse of the hypothesis is true, so we can say:
$$
|\{p|p \text{ is prime}\}| = \infty
$$

#### Induction

Hypothesize:
$$
n \in \mathbb{N}
$$

Then we show the base case:
$$
n = 0 \implies \sum_{i = 0}^0 i = 0 = 0 \cdot \frac{0 + 1}{2}
$$

And the inductive case:
$$
\sum_{i = 1}^{n - 1} i = \frac{n((n - 1) + 1)}{2} \implies \\
\sum_{i = 1}^n i = n + \sum_{i = 1}^{n - 1} i = n + \frac{(n - 1)((n - 1) + 1)}{2} \\
= \frac{2n + (n - 1)n}{2} = \frac{2n + n^2 - n}{2} = \frac{n(n + 1)}{2}
$$

A built in transformation lets us take a statement about $n = 0$ and $P(n - 1) \implies P(n)$ and say that $\forall n \in \mathbb{N} \enspace P(n)$.  


## Primitives

- `Object`
- `SimpleType`
- `CompoundType`
- `Statement`
- `Quantifier`
- `Variable`
- `Scope`

### Examples

$$
\forall = \in =_\mathbb{C} \enspace \forall + \in +_\mathbb{C} \enspace \forall x \in \mathbb{C} \enspace \forall y \in \mathbb{C} \\
\exists z \in \mathbb{C} \enspace x + y = z
$$

- $=, +, x, y, z$ are `Variable`s
- $\forall$ and $\exists$ are `Quantifier`s.  
- $\mathbb{C}$ is a `SimpleType` and a trivial `CompoundType`.  
- $=_\mathbb{C}, +_\mathbb{C}$ are `CompoundType`s that are subtypes of $(\mathbb{C}, \mathbb{C}, \mathbb{C})$.  
- The `Scope` is $\forall = \in =_\mathbb{C} \enspace \forall + \in +_\mathbb{C} \enspace  \forall x \in \mathbb{C} \enspace \forall y \in \mathbb{C} \enspace \exists z \in \mathbb{C}$.  
- $x + y = z$ is a `Predicate`.  
- The whole line is a `Statement`.  

A `Transformation` is a rule for mapping one `Statement` to another, where `Variables` may be carried over, eliminated, or new ones may be produced.  

### Examples

In order to encode the proof by induction transformation, we would create a generic transformation over $P \subset \mathbb{N}$ where:
$$
\forall 0 \in 0 \enspace \forall n \in \mathbb{N} \enspace 0 \in P \land ((n - 1) \in P \implies n \in P) \\
\implies
\forall n \in \mathbb{N} \enspace \exists p \in P \enspace n = p
$$