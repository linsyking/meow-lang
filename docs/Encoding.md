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

## Cat

We want `cat` to concatenate two strings. It is possible by using `rep2`.

```meow
cat(x,y) {
    rep2("\$","\",x,"$",y)
}

rep2(s,x1,y1,x2,y2) {
    var s1 = {
        "\$$" = enc(y1);
        "\$$$" = enc(y2);
        "\$$$$" = enc(x2) + "$";
        enc(x2) = "\$$$";
        enc(x1) = "\$$";
        enc(s)
    };
    dec(s1)
}

```

## Code

```meow
enc(x) {
    "$" = "\$";
    "\" = "\\";
    x
}

dec(x) {
    "\\" = "\";
    "\$" = "$";
    x
}
```
