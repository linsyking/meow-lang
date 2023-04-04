# i Expressions

i expressions allow you to evaluate cat expression inside cat expression. This gives us the power to do recursion.

The fibonacci function can be defined as:

```meow
fib(x) {
    if(
        eq(x, zero()),
        zero(),
        !(if(
            leq(x, num("2")),
            spack(num("1")),
            `add fib pred x fib pred pred x`
        ))
    )
}
```

The `!` operator is used to evaluate the expression inside.

You can try it in repl:

```
> ! `"23"`
23
> ! `cat "12" "22"`
1222
```

Note that `cat "12" "22"` itself is a string literal rather than many tokens.
