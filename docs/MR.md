# Multiple Replacement

It is easy to replace one string with another in meow. However, when you want to replace multiple strings with multiple strings, it is not that easy. This is because the replacement is done in a single pass.

For example,

```catlet
> let "a" "b" let "c" "a" "ac"
bb
```

We want to replace `a` with `b` and `c` with `a`. However, the replacement is done in a single pass, so the first replacement is done, and then the second replacement is done. So, the result is `bb`.

What if we want to do the replacement simultaneously? It's not easy to see.

This feature doesn't need i expression and it is originally designed to be supported in catlet.

First, we have to make sure that the multiple strings are all **independent**. Otherwise the result is not expected.

Implementation code for 2 strings:

```meow
encat(x,y) {
    {"#$"=""; x} + {"$#"=""; y}
}

enraw(s) {
    "#$" = "";
    "$#" = "";
    encode(s)
}

enrep(s,x,y) {
    enraw(x) = y;
    s
}

rep2(s,x,xr,y,yr) {
    var repx = enrep(encode(s),x,"x#");
    var repy = enrep(repx,y,"y#");
    decode({
        "x#" = enraw(xr);
        "y#" = enraw(yr);
        repy
    })
}
```
