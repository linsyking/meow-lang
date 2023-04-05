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

## Code

```meow
encode(s) {
    var rep = {
        "$" = "\$";
        "#" = "\#";
        "\" = "\\";
        s
    };
    "#$"+ rep +"$#"
}

decode(s) {
    var rep = {
        "$#" = "";
        "#$" = "";
        s
    };
    "\\" = "\";
    "\#" = "#";
    "\$" = "$";
    rep
}
```
