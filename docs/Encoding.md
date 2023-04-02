# Encoding

Think about two problems:

1. How to write a macro to decide whether two strings are equal?
2. How to write a `if` macro to do the conditional execution? More specifically, write a macro `if(c,x,y)`, it returns `x` if `c` is true, and `y` if `c` is false (assume that `c` can either be true or false).

First, we define true and false by:

```meow
true() {"T"}

false() {"F"}
```

They are represented by string literals.

To directly implement the `eq` macro is quite hard.

We have to first implement the `encode` and `decode` macro to help us.

## Encoding

Encoding means to encode a string into another string that has some special properties that we can use.

We define it by this:

$$
\mathtt{encode}(s) = \mathtt{"\_\^{\,}"} + (\mathtt{["\backslash \backslash"/"\backslash"]["\backslash \$"/"\$"]["\backslash \^{\,}"/"\^{\,}"]}s) + \mathtt{"\_\$"}
$$

We can prove the following results:

1. $|x|=1 \land x \neq \mathtt{"\backslash"} \Rightarrow $ $x\mathtt{"\^{\,}"} \not\subset \mathtt{["\backslash \backslash"/"\backslash"]["\backslash \$"/"\$"]["\backslash \^{\,}"/"\^{\,}"]}s$, $x\mathtt{"\$"} \not\subset \mathtt{["\backslash \backslash"/"\backslash"]["\backslash \$"/"\$"]["\backslash \^{\,}"/"\^{\,}"]}s$

## Code

```meow
encode(s) {
    var rep = {
        "\" = "\\";
        "$" = "\$";
        "^" = "\^";
        s
    };
    "_^"+ rep +"_$"
}

decode(s) {
    var rep = {
        "_^" = "";
        "_$" = "";
        s
    };
    "\$" = "$";
    "\^" = "^";
    "\\" = "\";
    rep
}
```
