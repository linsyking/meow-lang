# String Operation

Definition of replacement:

$[a/b]c := \begin{cases}
    xa[a/b]y, \exist x, y,(b\not\subset x)\land (c=xby) \\
    c, \text{otherwise}
\end{cases}$

Double Replacement Lemma:

$[x/y]([y/x]y)=\begin{cases}
    y, x\subset y\\
    x, \text{otherwise}
\end{cases}$

Similar result:
$[x/yy]([yy/x]y)=y$
